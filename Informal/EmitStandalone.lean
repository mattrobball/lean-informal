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

Each command is classified by its Syntax kind and carried as a structured
`CommandEntry` through to the assembly phase — no string re-parsing needed.
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

-- ═══ Phase 3: Per-command extraction ═══

/-- Classification of a command extracted from a source file. -/
inductive CmdClass where
  | tfbDecl (isSorried : Bool)   -- TFB declaration; `isSorried` = proof body replaced
  | context                      -- namespace/end/open/variable/section/set_option/universe
  | skip                         -- non-TFB declaration or other command
  deriving Inhabited, BEq

/-- A classified command with its source text.
    The Syntax kind is preserved so Phase 4 can distinguish namespace/open/variable/etc.
    without re-parsing the source string. -/
structure CommandEntry where
  cls : CmdClass
  src : String               -- source text (with sorry injection if applicable)
  kind : SyntaxNodeKind      -- the Syntax kind from the InfoTree
  deriving Inhabited

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

/-- Process one source file: re-elaborate against project env, classify each command,
    extract source with sorry injection. Returns structured entries. -/
def processFile (source : String) (projectEnv : Environment)
    (tfbRangeMap : Std.HashMap String.Pos.Raw Name)
    (filePath : String) : IO (Array CommandEntry) := do
  let inputCtx := Parser.mkInputContext source filePath
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := { Command.mkState projectEnv messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let trees := finalState.commandState.infoState.trees.toArray
  let mut entries : Array CommandEntry := #[]
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
    let topKind := stx.getKind
    -- Skip header
    if topKind == ``Parser.Module.header then continue
    -- Match to TFB by byte position
    let mut declaredTFBName : Option Name := none
    for (pos, name) in tfbRangeMap do
      if pos >= cmdStart && pos < cmdEnd then
        declaredTFBName := some name
        break
    match declaredTFBName with
    | some tfbName =>
      let isThmInEnv := match projectEnv.find? tfbName with
        | some (.thmInfo _) => true
        | _ => false
      if hasSorryableKind stx || isThmInEnv then
        if let some (valStart, _) := findDeclVal? stx then
          let beforeVal := (Substring.Raw.mk source cmdStart valStart).toString
          entries := entries.push { cls := .tfbDecl true, src := beforeVal ++ " := sorry", kind := topKind }
        else
          entries := entries.push { cls := .tfbDecl true, src := cmdSrc, kind := topKind }
      else
        entries := entries.push { cls := .tfbDecl false, src := cmdSrc, kind := topKind }
    | none =>
      if isContextCmd stx then
        entries := entries.push { cls := .context, src := cmdSrc, kind := topKind }
      else
        entries := entries.push { cls := .skip, src := cmdSrc, kind := topKind }
  return entries

-- ═══ Phase 4: Assembly ═══

/-- A module's classified content for assembly. -/
structure ModuleContent where
  modName : Name
  entries : Array CommandEntry
  deriving Inhabited

/-- Extract the "context signature" from a module's entries: the sequence of
    namespace/open/noncomputableSection commands (not variable/end/section). -/
def coreContextSignature (entries : Array CommandEntry) : Array SyntaxNodeKind := Id.run do
  let mut sig : Array SyntaxNodeKind := #[]
  for e in entries do
    match e.cls with
    | .context =>
      if e.kind == ``Parser.Command.namespace ||
         e.kind == ``Parser.Command.open then
        sig := sig.push e.kind
    | _ => pure ()
  sig

def emitStandalone (env : Environment) (rootPrefix : Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  -- Phase 1: TFB names
  let tfbNames ← match computeTFBNames env rootPrefix targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"TFB: {tfbNames.size} declarations"

  -- Phase 2: Module order from env.header.moduleNames (= import DAG order).
  -- Verified in Lean/Environment.lean:2120-2123: `importModulesCore` calls `goRec mod`
  -- (which recursively imports dependencies) BEFORE pushing the module name to
  -- `moduleNames`. So the array is in dependency-first topological order.
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
  let mut allModules : Array ModuleContent := #[]
  for modName in orderedModules do
    let filePath := modName.toString.replace "." "/" ++ ".lean"
    let source ← IO.FS.readFile filePath
    let fileMap := FileMap.ofString source
    let mut tfbRangeMap : Std.HashMap String.Pos.Raw Name := {}
    for name in tfbNames do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == modName then
          if let some ranges := findDeclRanges? env name then
            let bytePos := fileMap.ofPosition ranges.range.pos
            tfbRangeMap := tfbRangeMap.insert bytePos name
    IO.eprintln s!"  {filePath} ({tfbRangeMap.size} TFB decls)"
    let entries ← processFile source env tfbRangeMap filePath
    allModules := allModules.push { modName, entries }

  -- Phase 4: Assemble from structured entries
  -- Collect universes and set_options from context commands (using Syntax kind, not string parsing)
  let mut universeNames : Array String := #[]
  let mut setOptionSrcs : Std.HashMap String Nat := {}  -- src → count of modules containing it
  for mc in allModules do
    let mut seenInModule : Std.HashSet String := {}
    for e in mc.entries do
      match e.cls with
      | .context =>
        if e.kind == ``Parser.Command.universe then
          -- Extract universe names from the source (this is the one place we read the string,
          -- but the command was identified by Syntax kind, not string matching)
          for word in e.src.splitOn " " do
            let w := word.trimAsciiEnd.toString
            if w != "universe" && !w.isEmpty && !universeNames.contains w then
              universeNames := universeNames.push w
        if e.kind == ``Parser.Command.set_option && !seenInModule.contains e.src then
          seenInModule := seenInModule.insert e.src
          setOptionSrcs := setOptionSrcs.insert e.src ((setOptionSrcs.getD e.src 0) + 1)
      | _ => pure ()
  let numModules := allModules.size
  let mut hoistedOpts : Array String := #[]
  for (src, count) in setOptionSrcs do
    if count == numModules then hoistedOpts := hoistedOpts.push src

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

  -- Emit modules. Each module emits its context commands (from the source, including
  -- section/end pairs) and its TFB declarations. Context commands identified by Syntax
  -- kind; hoisted set_options and universes are skipped.
  for mc in allModules do
    let hasTFB := mc.entries.any fun e => match e.cls with | .tfbDecl _ => true | _ => false
    if !hasTFB then continue
    let shortName := mc.modName.toString.drop (rootPrefix.toString.length + 1)
    output := output ++ s!"-- ═══ {shortName} ═══\n\n"
    -- Emit context and declarations in source order
    for e in mc.entries do
      match e.cls with
      | .context =>
        if e.kind == ``Parser.Command.universe then continue  -- hoisted to top
        if e.kind == ``Parser.Command.set_option && hoistedOpts.contains e.src then continue
        output := output ++ e.src ++ "\n"
      | .tfbDecl _ =>
        output := output ++ e.src ++ "\n"
      | .skip => pure ()

  -- Strip @[informal]/@[expose] from output (these attributes require importing Informal).
  -- We identify them by string prefix since they're embedded in declaration source text,
  -- not separate commands.
  let lines := output.splitOn "\n"
  let filtered := lines.filter fun line =>
    let t := line.trimAsciiStart.toString
    !(t.startsWith "@[informal " || t.startsWith "@[expose]")
  output := "\n".intercalate filtered

  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"

end Informal.EmitStandalone

elab "#emit_standalone" root:ident target:ident path:str : command => do
  let env ← getEnv
  Informal.EmitStandalone.emitStandalone env root.getId target.getId path.getString

end
