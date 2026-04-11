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

Uses InfoTree re-elaboration to extract original Syntax for each command, with
surgical `declVal` replacement for sorry injection. Each source file is
re-elaborated independently via `IO.processCommands`. Declarations ordered by
Kahn's topological sort.
-/

public meta section

open Lean Elab Command Meta Informal

namespace Informal.EmitStandalone

-- ═══ Phase 1: TFB name computation ═══

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

-- ═══ Phase 2: Topological sort (Kahn's algorithm) ═══

def directDepsInSet (env : Environment) (name : Name) (relevantNames : Std.HashSet Name)
    : Array Name := Id.run do
  let some ci := env.find? name | return #[]
  let used := usedConstants ci (proofIrrelevant := true)
  let mut deps : Array Name := #[]
  for u in used.toArray do
    let resolved := resolveToUser env u
    if relevantNames.contains resolved && resolved != name then
      deps := deps.push resolved
  deps.toList.eraseDups.toArray

def topologicalSort (env : Environment) (names : Std.HashSet Name) : Array Name := Id.run do
  let nameArray := names.toArray
  let mut deps : Std.HashMap Name (Array Name) := {}
  let mut inDegree : Std.HashMap Name Nat := {}
  for n in nameArray do
    inDegree := inDegree.insert n 0
  for n in nameArray do
    let d := directDepsInSet env n names
    deps := deps.insert n d
    for dep in d do
      inDegree := inDegree.insert dep ((inDegree.getD dep 0) + 1)
  let mut queue : Array Name := #[]
  for n in nameArray do
    if (inDegree.getD n 0) == 0 then
      queue := queue.push n
  let mut result : Array Name := #[]
  while !queue.isEmpty do
    let n := queue.back!
    queue := queue.pop
    result := result.push n
    for dep in (deps.getD n #[]) do
      let newDeg := (inDegree.getD dep 1) - 1
      inDegree := inDegree.insert dep newDeg
      if newDeg == 0 then
        queue := queue.push dep
  for n in nameArray do
    if !result.contains n then
      result := result.push n
  result.reverse

-- ═══ Phase 3: InfoTree-based source extraction ═══

/-- Find a `declVal` node in a Syntax tree (worklist BFS). -/
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

/-- Check whether a declaration needs its body sorry'd. -/
def needsSorry (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.thmInfo _) => true
  | some (.defnInfo _) =>
    if (Lean.getReducibilityStatusCore env name) == .reducible then false
    else true
  | some (.opaqueInfo _) => false
  | _ => false

/-- Re-elaborate a source file and extract TFB-relevant content with sorry injection.

    Uses `IO.processCommands` (one file at a time) to get the full command
    list and InfoTrees. Walks the `Frontend.State.commands` array paired with
    environment snapshots from InfoTrees to identify which commands declare
    TFB names. -/
def processFile (filePath : System.FilePath) (tfbNames : Std.HashSet Name)
    (projectEnv : Environment) : IO String := do
  IO.eprintln s!"  Re-elaborating {filePath}"
  let input ← IO.FS.readFile filePath
  let inputCtx := Parser.mkInputContext input filePath.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← Elab.processHeader header {} messages inputCtx (trustLevel := 1024)
  let cmdState := { Command.mkState env messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState
  -- Get all commands (except EOI) and all InfoTrees
  let commands := finalState.commands.pop  -- Remove terminal EOI
  let trees := finalState.commandState.infoState.trees.toArray
  let mut output := ""
  -- Walk each InfoTree to get CommandInfo with env before/after
  for tree in trees do
    -- Extract the outermost CommandInfo from this tree
    let cmdResult := tree.foldInfo (init := none) fun ctx info acc =>
      match acc with
      | some _ => acc
      | none =>
        match info with
        | .ofCommandInfo ci => some (ci.stx, ctx.env, ctx.cmdEnv?.getD ctx.env)
        | _ => none
    let some (stx, envBefore, envAfter) := cmdResult | continue
    let some cmdStart := stx.getPos? | continue
    let some cmdEnd := stx.getTailPos? | continue
    let cmdSrc := (Substring.Raw.mk input cmdStart cmdEnd).toString
    -- Skip header
    if stx.getKind == ``Parser.Module.header then continue
    -- Check if this command declared any TFB names
    let mut declaredTFBName : Option Name := none
    for name in tfbNames do
      if envAfter.contains name && !envBefore.contains name then
        declaredTFBName := some name
        break
    match declaredTFBName with
    | some name =>
      if needsSorry projectEnv name && hasSorryableKind stx then
        if let some (valStart, valEnd) := findDeclVal? stx then
          -- Emit source before declVal, then sorry
          let beforeVal := (Substring.Raw.mk input cmdStart valStart).toString
          output := output ++ beforeVal ++ " := sorry\n"
        else
          output := output ++ cmdSrc ++ "\n"
      else
        output := output ++ cmdSrc ++ "\n"
    | none =>
      if isContextCmd stx then
        output := output ++ cmdSrc ++ "\n"
  return output

-- ═══ Phase 4: Assembly ═══

def emitStandalone (env : Environment) (rootPrefix : Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  let tfbNames ← match computeTFBNames env rootPrefix targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"TFB: {tfbNames.size} declarations"
  let sorted := topologicalSort env tfbNames
  -- Module order from topologically sorted declarations
  let mut seenModules : Array Name := #[]
  let mut moduleSet : Std.HashSet Name := {}
  for name in sorted do
    match env.getModuleIdxFor? name with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if !moduleSet.contains modName then
        seenModules := seenModules.push modName
        moduleSet := moduleSet.insert modName
    | none => pure ()
  IO.eprintln s!"TFB spans {seenModules.size} modules"
  let mut fileContents : Array String := #[]
  for modName in seenModules do
    let filePath := modName.toString.replace "." "/" ++ ".lean"
    let content ← processFile filePath tfbNames env
    if !content.trimAsciiEnd.toString.isEmpty then
      let shortName := modName.toString.drop (rootPrefix.toString.length + 1)
      fileContents := fileContents.push (s!"\n-- ═══ {shortName} ═══\n" ++ content)
  let mut output := ""
  output := output ++ "import Mathlib\n\n"
  output := output ++ "/-! # Trusted Formalization Base\n"
  output := output ++ s!"{rootPrefix} — `{targetName}`\n"
  output := output ++ s!"Auto-generated — all proofs replaced with `sorry`.\n"
  output := output ++ s!"{tfbNames.size} declarations in dependency order.\n"
  output := output ++ "-/\n"
  for content in fileContents do
    output := output ++ content
  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"

end Informal.EmitStandalone

elab "#emit_standalone" root:ident target:ident path:str : command => do
  let env ← getEnv
  Informal.EmitStandalone.emitStandalone env root.getId target.getId path.getString

end
