/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard, Formalization
-/
module

public meta import Informal.Deps
public meta import Informal.Classify
public meta import Lean

/-!
# Standalone TFB file generator

Given a compiled Lean environment and a target declaration name, generates a
single standalone `.lean` file containing all transitive type-level dependencies
(the Trusted Formalization Base) with proofs replaced by `sorry`.

Uses parse-only Syntax trees (no re-elaboration) to locate `declVal` nodes
for precise sorry injection. Declaration identification uses `DeclarationRanges`
from the pre-compiled environment.
-/

public meta section

open Lean Elab Command Meta Informal

namespace Informal.EmitStandalone

-- ═══ Phase 1: TFB name computation ═══

/-- Compute the TFB name set: transitive type-level dependencies of a target
declaration, filtered to project-local user-facing declarations. -/
def computeTFBNames (env : Environment) (rootPrefix : Name) (targetName : Name)
    (excludePrefixes : Array Name := #[]) : Except String (Std.HashSet Name) := do
  let some ci := env.find? targetName
    | .error s!"Target declaration '{targetName}' not found in environment"
  let rawDeps := collectDeps env targetName ci (proofIrrelevant := true)
  let mut result : Std.HashSet Name := {}
  result := result.insert targetName
  for dep in rawDeps.toArray do
    let resolved := resolveToUser env dep
    match env.getModuleIdxFor? resolved with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if rootPrefix.isPrefixOf modName
          && !excludePrefixes.any (·.isPrefixOf modName)
          && (classifyNonUser env resolved).isNone then
        result := result.insert resolved
    | none => pure ()
  return result

-- ═══ Phase 2: Helpers ═══

/-- Order modules by the import DAG (dependencies first). -/
def orderModules (env : Environment) (modules : Array Name) : Array Name := Id.run do
  let mut modIdxMap : Std.HashMap Name Nat := {}
  for i in [:env.header.moduleNames.size] do
    modIdxMap := modIdxMap.insert env.header.moduleNames[i]! i
  let indexed := modules.filterMap fun m => (modIdxMap[m]?).map (m, ·)
  let sorted := indexed.qsort fun a b => a.2 < b.2
  sorted.map (·.1)

/-- Look up declaration ranges from the environment extension. -/
def findDeclRanges? (env : Environment) (name : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env name <|>
    declRangeExt.find? (level := .server) env name

/-- Check whether a declaration needs its body sorry'd. -/
def needsSorry (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.thmInfo _) => true
  | some (.defnInfo _) =>
    if (Lean.getReducibilityStatusCore env name) == .reducible then false
    else true
  | some (.opaqueInfo _) => false
  | _ => false

/-- A source replacement entry. -/
structure Replacement where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  newValue : String
  deriving Inhabited

/-- Find a `declVal` node in a Syntax tree using worklist search. -/
def findDeclVal? (root : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.declValSimple ||
       k == ``Parser.Command.declValEqns ||
       k == ``Parser.Command.whereStructInst then
      match stx.getPos?, stx.getTailPos? with
      | some s, some e => return some (s, e)
      | _, _ => pure ()
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return none

/-- Check if a Syntax contains a sorry-able declaration kind. -/
def hasSorryableKind (root : Syntax) : Bool := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.theorem ||
       k == ``Parser.Command.definition ||
       k == ``Parser.Command.instance then
      return true
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return false

/-- Check if a Syntax is a context-setting command. -/
def isContextCmd (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Parser.Command.namespace ||
  k == ``Parser.Command.«end» ||
  k == ``Parser.Command.open ||
  k == ``Parser.Command.variable ||
  k == ``Parser.Command.«section» ||
  k == ``Parser.Command.set_option ||
  k == ``Parser.Command.universe ||
  k == ``Parser.Command.attribute

-- ═══ Phase 3: Parse and classify ═══

/-- Describes what to do with a command's source range. -/
inductive CommandAction where
  | keep
  | keepWithSorry (r : Replacement)
  | skip
  deriving Inhabited

/-- Parse a source file (no elaboration) and classify each command.
    Uses DeclarationRanges from the pre-compiled environment to match
    parsed commands to TFB declarations. -/
def classifyCommandsParsed (env : Environment) (fullEnv : Environment) (filePath : System.FilePath)
    (tfbRangeMap : Std.HashMap String.Pos.Raw Name) : IO (Array (String.Pos.Raw × String.Pos.Raw × CommandAction)) := do
  -- Parse (no elaboration) — fast, uses fullEnv for token/notation tables
  let moduleSyntax ← Parser.testParseFile fullEnv filePath
  let stx := moduleSyntax.raw
  -- stx is `Lean.Parser.Module.module` with children [header, commandList]
  let args := stx.getArgs
  let header := args[0]!  -- Module.header
  let cmdList := args[1]! -- nullNode of commands

  let mut actions : Array (String.Pos.Raw × String.Pos.Raw × CommandAction) := #[]

  -- Skip the header (imports)
  if let (some hs, some he) := (header.getPos?, header.getTailPos?) then
    actions := actions.push (hs, he, .skip)

  -- Classify each command
  for cmd in cmdList.getArgs do
    let some cmdStart := cmd.getPos? | continue
    let some cmdEnd := cmd.getTailPos? | continue

    -- Is it a context command?
    if isContextCmd cmd then
      actions := actions.push (cmdStart, cmdEnd, .keep)
      continue

    -- Does this command's range overlap with any TFB declaration?
    -- Check if any TFB declaration starts within this command's byte range
    let mut declaresTFB := false
    let mut tfbName : Name := .anonymous
    for (pos, name) in tfbRangeMap do
      if pos >= cmdStart && pos < cmdEnd then
        declaresTFB := true
        tfbName := name
        break

    if declaresTFB then
      if needsSorry env tfbName && hasSorryableKind cmd then
        if let some (valStart, valEnd) := findDeclVal? cmd then
          actions := actions.push (cmdStart, cmdEnd,
            .keepWithSorry { startPos := valStart, endPos := valEnd, newValue := " := sorry" })
        else
          actions := actions.push (cmdStart, cmdEnd, .keep)
      else
        actions := actions.push (cmdStart, cmdEnd, .keep)
    else
      actions := actions.push (cmdStart, cmdEnd, .skip)

  return actions

/-- Apply classified actions to source text. -/
def applyActions (source : String)
    (actions : Array (String.Pos.Raw × String.Pos.Raw × CommandAction)) : String := Id.run do
  let sorted := actions.qsort fun a b => a.1 < b.1
  let mut result := ""
  for (cmdStart, cmdEnd, action) in sorted do
    match action with
    | .skip => pure ()
    | .keep =>
      result := result ++ (Substring.Raw.mk source cmdStart cmdEnd).toString ++ "\n"
    | .keepWithSorry r =>
      result := result ++ (Substring.Raw.mk source cmdStart r.startPos).toString
      result := result ++ r.newValue ++ "\n"
  result

-- ═══ Phase 4: Assembly ═══

/-- Process a single module. -/
def processModule (env : Environment) (fullEnv : Environment) (modName : Name)
    (rootPrefix : Name) (declNames : Array Name) : IO (Option String) := do
  let sourcePath := modName.toString.replace "." "/" ++ ".lean"

  -- Build a map from source byte position → TFB name for this module
  let source ← IO.FS.readFile sourcePath
  let fileMap := FileMap.ofString source
  let mut tfbRangeMap : Std.HashMap String.Pos.Raw Name := {}
  for name in declNames do
    if let some ranges := findDeclRanges? env name then
      let bytePos := fileMap.ofPosition ranges.range.pos
      tfbRangeMap := tfbRangeMap.insert bytePos name

  IO.eprintln s!"  Parsing {sourcePath} ({declNames.size} TFB decls)"
  let actions ← classifyCommandsParsed env fullEnv sourcePath tfbRangeMap
  let content := applyActions source actions
  if content.trimAsciiEnd.toString.isEmpty then return none
  let shortName := modName.toString.drop (rootPrefix.toString.length + 1)
  return some (s!"\n-- ═══ {shortName} ═══\n" ++ content)

/-- Main entry point: generate a standalone TFB file. -/
def emitStandalone (env : Environment) (rootPrefix : Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  let tfbNames ← match computeTFBNames env rootPrefix targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"TFB: {tfbNames.size} declarations"

  let mut moduleMap : Std.HashMap Name (Array Name) := {}
  for name in tfbNames do
    match env.getModuleIdxFor? name with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      moduleMap := moduleMap.insert modName
        ((moduleMap.getD modName #[]).push name)
    | none => IO.eprintln s!"  Warning: no module for {name}"
  let orderedModules := orderModules env (moduleMap.toArray.map (·.1))
  IO.eprintln s!"TFB spans {orderedModules.size} modules"

  let mut fileContents : Array String := #[]
  for modName in orderedModules do
    let some declNames := moduleMap[modName]? | continue
    let some content ← processModule env env modName rootPrefix declNames
      | continue
    fileContents := fileContents.push content

  let mut output := ""
  output := output ++ "import Mathlib\n\n"
  output := output ++ "/-! # Trusted Formalization Base\n"
  output := output ++ s!"{rootPrefix} — `{targetName}`\n"
  output := output ++ "Auto-generated — all proofs replaced with `sorry`.\n"
  output := output ++ "-/\n"
  for content in fileContents do
    output := output ++ content
  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"

end Informal.EmitStandalone

/-- `#emit_standalone rootPrefix targetDecl "output.lean"` -/
elab "#emit_standalone" root:ident target:ident path:str : command => do
  let env ← getEnv
  Informal.EmitStandalone.emitStandalone env root.getId target.getId path.getString

end
