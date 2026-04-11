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

No annotations or special markup required in the source repo.

Follows the compfiles (`dwrensha/compfiles`) pattern of working with original
source text and applying targeted replacements, but discovers TFB declarations
automatically via `collectDeps`. Uses `IO.processCommands` to re-elaborate
source files, walking the InfoTree to find `declVal` Syntax nodes for precise
sorry injection.
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

-- ═══ Phase 2: Source file processing ═══

/-- Order modules by the import DAG (dependencies first). -/
def orderModules (env : Environment) (modules : Array Name) : Array Name := Id.run do
  let mut modIdxMap : Std.HashMap Name Nat := {}
  for i in [:env.header.moduleNames.size] do
    modIdxMap := modIdxMap.insert env.header.moduleNames[i]! i
  let indexed := modules.filterMap fun m => (modIdxMap[m]?).map (m, ·)
  let sorted := indexed.qsort fun a b => a.2 < b.2
  sorted.map (·.1)

/-- Check whether a declaration needs its body sorry'd.
    Structures, classes, inductives, and abbrevs keep their bodies.
    Theorems, defs, and instances get sorry'd. -/
def needsSorry (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.thmInfo _) => true
  | some (.defnInfo _) =>
    if (Lean.getReducibilityStatusCore env name) == .reducible then false
    else true
  | some (.opaqueInfo _) => false
  | _ => false

/-- A source replacement entry (compfiles pattern). -/
structure Replacement where
  startPos : String.Pos
  endPos : String.Pos
  newValue : String
  deriving Inhabited

/-- Recursively search a Syntax tree for a `declVal` node (declValSimple,
    declValEqns, or whereStructInst) and return its source range. -/
partial def findDeclVal? (stx : Syntax) : Option (String.Pos × String.Pos) :=
  let k := stx.getKind
  if k == ``Parser.Command.declValSimple ||
     k == ``Parser.Command.declValEqns ||
     k == ``Parser.Command.whereStructInst then
    match stx.getPos?, stx.getTailPos? with
    | some s, some e => some (s, e)
    | _, _ => none
  else
    stx.getArgs.findSome? findDeclVal?

/-- Check if a Syntax is a declaration kind that should be sorry'd
    (theorem, def, instance — NOT structure, class, inductive, abbrev). -/
def isDeclKindToSorry (stx : Syntax) : Bool :=
  let rec check (s : Syntax) : Bool :=
    let k := s.getKind
    k == ``Parser.Command.theorem ||
    k == ``Parser.Command.definition ||
    k == ``Parser.Command.instance ||
    s.getArgs.any check
  check stx

/-- Check if a Syntax is a context-setting command (namespace, open, variable, etc.). -/
def isContextCmd (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Parser.Command.namespace ||
  k == ``Parser.Command.«end» ||
  k == ``Parser.Command.open ||
  k == ``Parser.Command.variable ||
  k == ``Parser.Command.«section» ||
  k == ``Parser.Command.noncomputableSection ||
  k == ``Parser.Command.set_option ||
  k == ``Parser.Command.universe ||
  k == ``Parser.Command.attribute

/-- Check if a Syntax is an import or module header. -/
def isHeaderCmd (stx : Syntax) : Bool :=
  stx.getKind == ``Parser.Module.header

-- ═══ Phase 3: Re-elaborate and extract ═══

/-- Describes what to do with a command's source range. -/
inductive CommandAction where
  | keep                         -- emit verbatim
  | keepWithSorry (r : Replacement) -- emit with sorry replacement
  | skip                         -- omit entirely
  deriving Inhabited

/-- Process a source file by re-elaborating it to get command Syntax trees.
    Returns a list of actions to apply to the source text. -/
def classifyCommands (env : Environment) (filePath : System.FilePath)
    (tfbNames : Std.HashSet Name) : IO (Array (String.Pos × String.Pos × CommandAction)) := do
  let source ← IO.FS.readFile filePath
  let inputCtx := Parser.mkInputContext source filePath.toString

  -- Parse header
  let (header, parserState, messages) := Parser.parseHeader inputCtx
  -- Process imports to get the file's environment
  let (headerEnv, messages) ← Elab.processHeader header {} messages inputCtx (trustLevel := 1024)
  let cmdState := Command.mkState headerEnv messages {}

  -- Process all commands
  let finalState ← IO.processCommands inputCtx parserState cmdState

  -- Walk InfoTrees to classify each command
  let trees := finalState.commandState.infoState.trees
  let mut actions : Array (String.Pos × String.Pos × CommandAction) := #[]

  for tree in trees do
    -- Each top-level tree is: context (commandCtx ...) (node (ofCommandInfo ...) ...)
    -- Extract command info from the root
    let result := tree.foldInfo (init := none) fun ctx info acc =>
      match acc with
      | some _ => acc  -- already found
      | none =>
        match info with
        | .ofCommandInfo ci =>
          -- Get the env before and after this command
          let envBefore := ctx.env
          let envAfter := ctx.cmdEnv?.getD ctx.env
          some (ci.stx, envBefore, envAfter)
        | _ => none
    let some (stx, envBefore, envAfter) := result | continue
    let some cmdStart := stx.getPos? | continue
    let some cmdEnd := stx.getTailPos? | continue

    -- Skip header (imports/module)
    if isHeaderCmd stx then
      actions := actions.push (cmdStart, cmdEnd, .skip)
      continue

    -- Check if this command is a context command
    if isContextCmd stx then
      actions := actions.push (cmdStart, cmdEnd, .keep)
      continue

    -- Check if this command declared any TFB names
    -- by diffing envAfter vs envBefore
    let mut declaresTFB := false
    let mut declaredTFBName : Name := .anonymous
    for name in tfbNames do
      if envAfter.contains name && !envBefore.contains name then
        declaresTFB := true
        declaredTFBName := name
        break

    if declaresTFB then
      -- Check if we need to sorry the body
      if needsSorry envAfter declaredTFBName && isDeclKindToSorry stx then
        -- Find the declVal node in the Syntax tree
        if let some (valStart, valEnd) := findDeclVal? stx then
          actions := actions.push (cmdStart, cmdEnd,
            .keepWithSorry { startPos := valStart, endPos := valEnd, newValue := " := sorry" })
        else
          -- No declVal found (e.g., opaque) — keep as-is
          actions := actions.push (cmdStart, cmdEnd, .keep)
      else
        -- Structure/class/inductive/abbrev — keep verbatim
        actions := actions.push (cmdStart, cmdEnd, .keep)
    else
      -- Not a TFB declaration — skip
      actions := actions.push (cmdStart, cmdEnd, .skip)

  return actions

/-- Apply classified actions to a source file, producing the filtered+sorry'd output. -/
def applyActions (source : String) (actions : Array (String.Pos × String.Pos × CommandAction))
    : String := Id.run do
  -- Sort actions by start position
  let sorted := actions.qsort fun a b => a.1 < b.1
  let mut result := ""
  for (cmdStart, cmdEnd, action) in sorted do
    match action with
    | .skip => pure ()
    | .keep =>
      result := result ++ (Substring.mk source cmdStart cmdEnd).toString ++ "\n"
    | .keepWithSorry r =>
      -- Emit text before the declVal, then the sorry replacement, skip the rest
      result := result ++ (Substring.mk source cmdStart r.startPos).toString
      result := result ++ r.newValue ++ "\n"
  result

-- ═══ Phase 4: Assembly ═══

/-- Process a single module: re-elaborate, classify commands, apply actions. -/
def processModule (env : Environment) (modName : Name) (rootPrefix : Name)
    (tfbNames : Std.HashSet Name) : IO (Option String) := do
  let sourcePath := modName.toString.replace "." "/" ++ ".lean"
  IO.eprintln s!"  Re-elaborating {sourcePath}"
  let actions ← classifyCommands env sourcePath tfbNames
  let source ← IO.FS.readFile sourcePath
  let content := applyActions source actions
  if content.trimRight.isEmpty then return none
  let shortName := modName.toString.drop (rootPrefix.toString.length + 1)
  return some (s!"\n-- ═══ {shortName} ═══\n" ++ content)

/-- Main entry point: generate a standalone TFB file. -/
def emitStandalone (env : Environment) (rootPrefix : Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  -- Phase 1: Compute TFB names
  let tfbNames ← match computeTFBNames env rootPrefix targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"TFB: {tfbNames.size} declarations"

  -- Phase 2: Group by module, order by import DAG
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

  -- Phase 3: Process each module
  let mut fileContents : Array String := #[]
  for modName in orderedModules do
    let some content ← processModule env modName rootPrefix tfbNames
      | continue
    fileContents := fileContents.push content

  -- Phase 4: Assemble final file
  let mut output := ""
  output := output ++ "import Mathlib\n"
  output := output ++ "\n"
  output := output ++ "/-! # Trusted Formalization Base\n"
  output := output ++ s!"{rootPrefix} — `{targetName}`\n"
  output := output ++ "Auto-generated — all proofs replaced with `sorry`.\n"
  output := output ++ "-/\n"
  for content in fileContents do
    output := output ++ content
  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"

end Informal.EmitStandalone

/-- `#emit_standalone rootPrefix targetDecl "output.lean"` — generate a standalone
    TFB file from a compiled project. -/
elab "#emit_standalone" root:ident target:ident path:str : command => do
  let env ← getEnv
  let rootPrefix := root.getId
  let targetName := target.getId
  Informal.EmitStandalone.emitStandalone env rootPrefix targetName path.getString

end
