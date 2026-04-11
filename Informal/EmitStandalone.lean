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

Uses `IO.processCommands` to re-elaborate source files, walking the InfoTree
to find `declVal` Syntax nodes for precise sorry injection.
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

/-- Find a `declVal` node (declValSimple, declValEqns, whereStructInst) in a
    Syntax tree using a bounded worklist search.  Returns its source range. -/
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

/-- Check if a Syntax contains a theorem, def, or instance declaration
    (kinds that should have their bodies sorry'd). -/
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

-- ═══ Phase 3: Re-elaborate and classify ═══

/-- Describes what to do with a command's source range. -/
inductive CommandAction where
  | keep
  | keepWithSorry (r : Replacement)
  | skip
  deriving Inhabited

/-- Process a source file by re-elaborating it. Returns classified command actions. -/
def classifyCommands (env : Environment) (filePath : System.FilePath)
    (tfbNames : Std.HashSet Name) : IO (Array (String.Pos.Raw × String.Pos.Raw × CommandAction)) := do
  let source ← IO.FS.readFile filePath
  let inputCtx := Parser.mkInputContext source filePath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (headerEnv, messages) ← Elab.processHeader header {} messages inputCtx (trustLevel := 1024)
  let cmdState := Command.mkState headerEnv messages {}
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let trees := finalState.commandState.infoState.trees
  let mut actions : Array (String.Pos.Raw × String.Pos.Raw × CommandAction) := #[]

  for tree in trees do
    -- Extract the outermost CommandInfo from each tree
    let result := tree.foldInfo (init := none) fun ctx info acc =>
      match acc with
      | some _ => acc
      | none =>
        match info with
        | .ofCommandInfo ci => some (ci.stx, ctx.env, ctx.cmdEnv?.getD ctx.env)
        | _ => none
    let some (stx, envBefore, envAfter) := result | continue
    let some cmdStart := stx.getPos? | continue
    let some cmdEnd := stx.getTailPos? | continue

    -- Skip file header
    if stx.getKind == ``Parser.Module.header then
      actions := actions.push (cmdStart, cmdEnd, .skip)
      continue

    -- Keep context commands
    if isContextCmd stx then
      actions := actions.push (cmdStart, cmdEnd, .keep)
      continue

    -- Check if this command declared any TFB names
    let mut declaresTFB := false
    let mut declaredName : Name := .anonymous
    for name in tfbNames do
      if envAfter.contains name && !envBefore.contains name then
        declaresTFB := true
        declaredName := name
        break

    if declaresTFB then
      if needsSorry envAfter declaredName && hasSorryableKind stx then
        if let some (valStart, valEnd) := findDeclVal? stx then
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
def applyActions (source : String) (actions : Array (String.Pos.Raw × String.Pos.Raw × CommandAction))
    : String := Id.run do
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
def processModule (env : Environment) (modName : Name) (rootPrefix : Name)
    (tfbNames : Std.HashSet Name) : IO (Option String) := do
  let sourcePath := modName.toString.replace "." "/" ++ ".lean"
  IO.eprintln s!"  Re-elaborating {sourcePath}"
  let actions ← classifyCommands env sourcePath tfbNames
  let source ← IO.FS.readFile sourcePath
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
    let some content ← processModule env modName rootPrefix tfbNames
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
