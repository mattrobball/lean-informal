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

Uses InfoTree re-elaboration (reusing the project env) to get per-command
Syntax. Matches commands to TFB declarations via DeclarationRanges byte
positions. Surgical `declVal` replacement for sorry injection.
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

-- ═══ Phase 3: Per-command extraction (tested in Test/ExtractTest.lean) ═══

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

def hasSorryableKind (root : Syntax) : Bool := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    -- Only sorry theorems/lemmas. Defs/instances keep their bodies
    -- because downstream code depends on definitional reduction.
    if k == ``Parser.Command.theorem then
      return true
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return false

def isContextCmd (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Parser.Command.namespace ||
  k == ``Parser.Command.«end» ||
  k == ``Parser.Command.open ||
  k == ``Parser.Command.variable ||
  k == ``Parser.Command.«section» ||
  k == ``Parser.Command.set_option ||
  k == ``Parser.Command.universe

def findDeclRanges? (env : Environment) (name : Name) : Option DeclarationRanges :=
  declRangeExt.find? (level := .exported) env name <|>
    declRangeExt.find? (level := .server) env name

/-- Process one source file: re-elaborate against project env, extract TFB
    declarations with sorry injection, keep minimal context commands. -/
def processFile (source : String) (projectEnv : Environment)
    (tfbRangeMap : Std.HashMap String.Pos.Raw Name)
    (filePath : String) : IO String := do
  let inputCtx := Parser.mkInputContext source filePath
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := { Command.mkState projectEnv messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let trees := finalState.commandState.infoState.trees.toArray
  let mut output := ""
  for i in [:trees.size] do
    let tree := trees[i]!
    let cmdResult := tree.foldInfo (init := none) fun _ctx info acc =>
      match acc with
      | some _ => acc
      | none =>
        match info with
        | .ofCommandInfo ci => some ci.stx
        | _ => none
    let some stx := cmdResult | continue
    let some cmdStart := stx.getPos? | continue
    let some cmdEnd := stx.getTailPos? | continue
    let cmdSrc := (Substring.Raw.mk source cmdStart cmdEnd).toString
    if stx.getKind == ``Parser.Module.header then continue
    -- Match to TFB by byte position
    let mut declaredTFBName : Option Name := none
    for (pos, name) in tfbRangeMap do
      if pos >= cmdStart && pos < cmdEnd then
        declaredTFBName := some name
        break
    match declaredTFBName with
    | some _name =>
      if hasSorryableKind stx then
        if let some (valStart, _) := findDeclVal? stx then
          let beforeVal := (Substring.Raw.mk source cmdStart valStart).toString
          output := output ++ beforeVal ++ " := sorry\n"
        else
          output := output ++ cmdSrc ++ "\n"
      else
        -- Structure/class/inductive/abbrev: keep verbatim
        output := output ++ cmdSrc ++ "\n"
    | none =>
      if isContextCmd stx then
        output := output ++ cmdSrc ++ "\n"
  return output

-- ═══ Phase 4: Assembly ═══

def emitStandalone (env : Environment) (rootPrefix : Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  -- Phase 1: TFB names
  let tfbNames ← match computeTFBNames env rootPrefix targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"TFB: {tfbNames.size} declarations"

  -- Phase 2: Module order from env.header.moduleNames (= import DAG order)
  let mut moduleSet : Std.HashSet Name := {}
  for name in tfbNames do
    if let some idx := env.getModuleIdxFor? name then
      moduleSet := moduleSet.insert env.header.moduleNames[idx.toNat]!
  let mut modIdxPairs : Array (Name × Nat) := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if moduleSet.contains modName then
      modIdxPairs := modIdxPairs.push (modName, i)
  let orderedModules := (modIdxPairs.qsort fun a b => a.2 < b.2).map (·.1)
  IO.eprintln s!"TFB spans {orderedModules.size} modules"

  -- Phase 3: Build tfbRangeMap per module and process each file
  let mut allContent : Array (Name × String) := #[]
  for modName in orderedModules do
    let filePath := modName.toString.replace "." "/" ++ ".lean"
    let source ← IO.FS.readFile filePath
    let fileMap := FileMap.ofString source
    -- Build range map for TFB names in this module
    let mut tfbRangeMap : Std.HashMap String.Pos.Raw Name := {}
    for name in tfbNames do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == modName then
          if let some ranges := findDeclRanges? env name then
            let bytePos := fileMap.ofPosition ranges.range.pos
            tfbRangeMap := tfbRangeMap.insert bytePos name
    IO.eprintln s!"  {filePath} ({tfbRangeMap.size} TFB decls)"
    let content ← processFile source env tfbRangeMap filePath
    if !content.trimAsciiEnd.toString.isEmpty then
      allContent := allContent.push (modName, content)

  -- Phase 4: Assemble with consolidated header
  let mut output := "import Mathlib\n\n"
  output := output ++ "/-! # Trusted Formalization Base\n"
  output := output ++ s!"{rootPrefix} — `{targetName}`\n"
  output := output ++ s!"Auto-generated — all proofs replaced with `sorry`.\n"
  output := output ++ s!"{tfbNames.size} declarations in dependency order.\n"
  output := output ++ "-/\n\n"
  output := output ++ "set_option maxHeartbeats 400000\n\n"
  for (modName, content) in allContent do
    let shortName := modName.toString.drop (rootPrefix.toString.length + 1)
    output := output ++ s!"-- ═══ {shortName} ═══\n"
    -- Strip duplicate universe declarations (they'll conflict across files)
    -- and @[informal]/@[expose] attributes
    let lines := content.splitOn "\n"
    let filtered := lines.filter fun line =>
      let t := line.trimAsciiStart.toString
      !(t.startsWith "universe " || t.startsWith "@[informal " || t.startsWith "@[expose]")
    output := output ++ "\n".intercalate filtered
    output := output ++ "\n"
  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"

end Informal.EmitStandalone

elab "#emit_standalone" root:ident target:ident path:str : command => do
  let env ← getEnv
  Informal.EmitStandalone.emitStandalone env root.getId target.getId path.getString

end
