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
    -- Only sorry theorems/lemmas. Everything else (defs, instances, abbrevs)
    -- keeps its body because type checking depends on definitional reduction.
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
    | some tfbName =>
      -- Sorry theorems (incl Prop-valued instances, which are thmInfo in the env).
      -- Data-valued defs/instances keep their bodies for type unification.
      let isThmInEnv := match projectEnv.find? tfbName with
        | some (.thmInfo _) => true
        | _ => false
      if hasSorryableKind stx || isThmInEnv then
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

  -- Phase 4: Assemble with consolidated header and merged contexts
  -- Classify each line as context vs content
  let isContextLine (t : String) : Bool :=
    t.startsWith "noncomputable section" ||
    t.startsWith "open " ||
    t.startsWith "namespace " ||
    t.startsWith "variable " ||
    t.startsWith "attribute " ||
    t.startsWith "end "
  let isStrippable (t : String) (hoistedOpts : Array String) : Bool :=
    t.startsWith "universe " ||
    t.startsWith "@[informal " ||
    t.startsWith "@[expose]" ||
    hoistedOpts.contains t
  -- Collect universes, find universal set_options
  let mut universeNames : Array String := #[]
  let mut setOptionCounts : Std.HashMap String Nat := {}
  let numSections := allContent.size
  for (_, content) in allContent do
    let mut seenInFile : Std.HashSet String := {}
    for line in content.splitOn "\n" do
      let t := line.trimAsciiStart.toString
      if t.startsWith "universe " then
        for name in (t.drop 9).toString.splitOn " " do
          let name := name.trimAsciiEnd.toString
          if !name.isEmpty && !universeNames.contains name then
            universeNames := universeNames.push name
      if t.startsWith "set_option " && !seenInFile.contains t then
        seenInFile := seenInFile.insert t
        setOptionCounts := setOptionCounts.insert t ((setOptionCounts.getD t 0) + 1)
  let mut hoistedOpts : Array String := #[]
  for (opt, count) in setOptionCounts do
    if count == numSections then hoistedOpts := hoistedOpts.push opt
  -- Extract context signature per section for merging
  -- A context signature = the set of context lines (noncomputable, open, namespace, variable)
  let extractContext (content : String) : Array String := Id.run do
    let mut ctx : Array String := #[]
    for line in content.splitOn "\n" do
      let t := line.trimAsciiStart.toString
      if isContextLine t && !isStrippable t hoistedOpts then
        ctx := ctx.push line
    ctx
  -- Extract non-context, non-strippable content lines
  let extractDecls (content : String) : Array String := Id.run do
    let mut decls : Array String := #[]
    for line in content.splitOn "\n" do
      let t := line.trimAsciiStart.toString
      if !isContextLine t && !isStrippable t hoistedOpts && !t.isEmpty then
        decls := decls.push line
    decls
  -- Emit header
  let mut output := "import Mathlib\n\n"
  output := output ++ "/-! # Trusted Formalization Base\n"
  output := output ++ s!"{rootPrefix} — `{targetName}`\n"
  output := output ++ s!"Auto-generated — all proofs replaced with `sorry`.\n"
  output := output ++ s!"{tfbNames.size} declarations in dependency order.\n"
  output := output ++ "-/\n\n"
  output := output ++ "set_option maxHeartbeats 400000\n"
  for opt in hoistedOpts do
    output := output ++ opt ++ "\n"
  output := output ++ "\n"
  unless universeNames.isEmpty do
    output := output ++ "universe " ++ " ".intercalate universeNames.toList ++ "\n\n"
  -- Emit sections, merging consecutive ones with identical context
  let mut prevContext : Array String := #[]
  let mut emittedVars : Std.HashSet String := {}
  for (modName, content) in allContent do
    let shortName := modName.toString.drop (rootPrefix.toString.length + 1)
    let ctx := extractContext content
    let decls := extractDecls content
    if decls.isEmpty then continue
    -- Check if context matches previous (can merge)
    -- Extract just namespace/noncomputable/open lines (not variable/end)
    let coreCtx := ctx.filter fun line =>
      let t := line.trimAsciiStart.toString
      t.startsWith "noncomputable" || t.startsWith "open " || t.startsWith "namespace "
    let prevCoreCtx := prevContext.filter fun line =>
      let t := line.trimAsciiStart.toString
      t.startsWith "noncomputable" || t.startsWith "open " || t.startsWith "namespace "
    if coreCtx == prevCoreCtx && !prevContext.isEmpty then
      -- Same context — just emit section header comment and declarations
      output := output ++ s!"\n-- ─── {shortName} ───\n"
      -- Emit any new variables not yet in scope
      for line in ctx do
        let t := line.trimAsciiStart.toString
        if t.startsWith "variable" && !emittedVars.contains t then
          output := output ++ line ++ "\n"
          emittedVars := emittedVars.insert t
    else
      -- Different context — close previous and open new
      if !prevContext.isEmpty then
        -- Emit end statements from previous context (reverse order)
        let prevNamespaces := prevContext.filter fun line =>
          line.trimAsciiStart.toString.startsWith "namespace "
        for ns in prevNamespaces.reverse do
          let nsName := (ns.trimAsciiStart.toString.drop 10).toString
          output := output ++ s!"end {nsName}\n"
        output := output ++ "\n"
      output := output ++ s!"-- ═══ {shortName} ═══\n"
      emittedVars := {}
      for line in ctx do
        let t := line.trimAsciiStart.toString
        if !t.startsWith "end " then  -- skip end lines in context
          output := output ++ line ++ "\n"
          if t.startsWith "variable" then
            emittedVars := emittedVars.insert t
    -- Emit declarations
    for line in decls do
      output := output ++ line ++ "\n"
    prevContext := ctx
  -- Close final context
  if !prevContext.isEmpty then
    let prevNamespaces := prevContext.filter fun line =>
      line.trimAsciiStart.toString.startsWith "namespace "
    for ns in prevNamespaces.reverse do
      let nsName := (ns.trimAsciiStart.toString.drop 10).toString
      output := output ++ s!"end {nsName}\n"
  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"

end Informal.EmitStandalone

elab "#emit_standalone" root:ident target:ident path:str : command => do
  let env ← getEnv
  Informal.EmitStandalone.emitStandalone env root.getId target.getId path.getString

end
