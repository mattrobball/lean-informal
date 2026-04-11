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
    (excludePrefixes : Array Name := #[])
    (importedEnv? : Option Environment := none) : Except String (Std.HashSet Name) := do
  let some ci := env.find? targetName
    | .error s!"Target declaration '{targetName}' not found in environment"
  let rawDeps := collectDeps env targetName ci (proofIrrelevant := true)
  let mut result : Std.HashSet Name := {}
  result := result.insert targetName
  for dep in rawDeps.toArray do
    let resolved := resolveToUser env dep
    -- Skip declarations already available from the import
    if let some impEnv := importedEnv? then
      if impEnv.contains resolved then continue
    match env.getModuleIdxFor? resolved with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if rootPrefix.isPrefixOf modName
          && !excludePrefixes.any (·.isPrefixOf modName)
          && (classifyNonUser env resolved).isNone then
        result := result.insert resolved
    | none => pure ()
  -- Also check if target itself is already imported
  if let some impEnv := importedEnv? then
    if impEnv.contains targetName then
      result := result.erase targetName
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

-- ═══ Configuration ═══

/-- How to handle macro-generated declarations in the skeleton. -/
inductive MacroHandling where
  /-- Expand: use `ppCommand` on the `MacroExpansionInfo` output to emit
      the expanded syntax. The reader sees the actual structure/def, not
      the macro call. -/
  | expand
  /-- Include: emit the original macro call and ensure the macro definition
      is pulled into the dependency walk so the call elaborates. -/
  | includeMacroDef
  deriving Inhabited, BEq

/-- Configuration for the TFB skeleton generator. -/
structure Config where
  /-- How to handle macro-generated declarations. -/
  macroHandling : MacroHandling := .expand
  deriving Inhabited

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
  startPos : String.Pos.Raw := 0  -- byte position in source file
  endPos : String.Pos.Raw := 0
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

/-- Check if a Syntax kind is a standard Lean command (not a custom macro). -/
def isStandardCmdKind (kind : SyntaxNodeKind) : Bool :=
  kind == ``Parser.Command.declaration ||
  kind == ``Parser.Module.header ||
  kind == ``Parser.Command.namespace ||
  kind == ``Parser.Command.«end» ||
  kind == ``Parser.Command.open ||
  kind == ``Parser.Command.variable ||
  kind == ``Parser.Command.«section» ||
  kind == ``Parser.Command.set_option ||
  kind == ``Parser.Command.universe

/-- Find a `MacroExpansionInfo` in an InfoTree whose output is a standard
    declaration. Returns the expanded Syntax if found. -/
def findMacroExpansion? (tree : InfoTree) : Option Syntax :=
  tree.foldInfo (init := none) fun _ctx info acc =>
    match acc with
    | some _ => acc
    | none =>
      match info with
      | .ofMacroExpansionInfo mei =>
        if mei.output.getKind == ``Parser.Command.declaration then
          some mei.output
        else none
      | _ => none

/-- Pretty-print a Syntax as a command string, stripping hygiene markers. -/
def ppCommandStr (env : Environment) (stx : Syntax) : IO String := do
  -- Strip macro scopes from all identifiers in the Syntax tree
  let rec stripScopes : Syntax → Syntax
    | .ident info rawVal name preresolved =>
      .ident info rawVal name.eraseMacroScopes preresolved
    | .node info kind args => .node info kind (args.map stripScopes)
    | other => other
  let cleaned := stripScopes stx
  let (fmt, _) ← (PrettyPrinter.ppCommand ⟨cleaned⟩).toIO
    { fileName := "<expand>", fileMap := default } { env }
  return fmt.pretty

/-- Process one source file: re-elaborate against project env, classify each command,
    extract source with sorry injection. Returns structured entries. -/
def processFile (source : String) (projectEnv : Environment)
    (tfbRangeMap : Std.HashMap String.Pos.Raw Name)
    (filePath : String) (cfg : Config := {}) : IO (Array CommandEntry) := do
  let inputCtx := Parser.mkInputContext source filePath
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := { Command.mkState projectEnv messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let trees := finalState.commandState.infoState.trees.toArray
  let mut entries : Array CommandEntry := #[]
  let mut neededMacroKinds : Std.HashSet SyntaxNodeKind := {}
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
      -- If this command is a macro (non-standard kind), handle per config
      let isMacroCmd := topKind != ``Parser.Command.declaration && !isContextCmd stx
      let mut effectiveSrc := cmdSrc
      let mut effectiveStx := stx
      if isMacroCmd then
        match cfg.macroHandling with
        | .expand =>
          if let some expandedStx := findMacroExpansion? tree then
            effectiveSrc ← ppCommandStr projectEnv expandedStx
            effectiveStx := expandedStx
        | .includeMacroDef =>
          -- Record macro kinds we need definitions for (collected after the loop)
          neededMacroKinds := neededMacroKinds.insert topKind
      let isThmInEnv := match projectEnv.find? tfbName with
        | some (.thmInfo _) => true
        | _ => false
      if hasSorryableKind effectiveStx || isThmInEnv then
        if let some (valStart, _) := findDeclVal? effectiveStx then
          if isMacroCmd && cfg.macroHandling == .expand then
            -- For expanded macros, sorry the whole thing
            entries := entries.push { startPos := cmdStart, endPos := cmdEnd, cls := .tfbDecl true, src := effectiveSrc, kind := topKind }
          else
            let beforeVal := (Substring.Raw.mk source cmdStart valStart).toString
            entries := entries.push { startPos := cmdStart, endPos := cmdEnd, cls := .tfbDecl true, src := beforeVal ++ " := sorry", kind := topKind }
        else
          entries := entries.push { startPos := cmdStart, endPos := cmdEnd, cls := .tfbDecl true, src := effectiveSrc, kind := topKind }
      else
        entries := entries.push { startPos := cmdStart, endPos := cmdEnd, cls := .tfbDecl false, src := effectiveSrc, kind := topKind }
    | none =>
      if isContextCmd stx then
        entries := entries.push { startPos := cmdStart, endPos := cmdEnd, cls := .context, src := cmdSrc, kind := topKind }
      else
        entries := entries.push { startPos := cmdStart, endPos := cmdEnd, cls := .skip, src := cmdSrc, kind := topKind }
  -- Second pass: for includeMacroDef mode, find macro definition commands
  -- for any macro kinds that TFB declarations need, and reclassify them
  -- from .skip to .context so they appear in the output.
  if cfg.macroHandling == .includeMacroDef && !neededMacroKinds.isEmpty then
    -- Look up macro declaration names via macroAttribute
    let mut neededDeclPositions : Std.HashSet String.Pos.Raw := {}
    let fileMap := FileMap.ofString source
    for kind in neededMacroKinds do
      for me in macroAttribute.getEntries projectEnv kind do
        if let some ranges := findDeclRanges? projectEnv me.declName then
          neededDeclPositions := neededDeclPositions.insert (fileMap.ofPosition ranges.range.pos)
    -- TODO: findDeclRanges? returns none for meta declarations when using
    -- importModules (ranges may only exist at .server level). This means
    -- includeMacroDef mode doesn't work from lake exe; it may work from
    -- the #emit_standalone elab command where the server populates ranges.
    -- For now, fall back to expand mode if no positions found.
    if neededDeclPositions.isEmpty then
      IO.eprintln s!"  Warning: could not find macro definition ranges for includeMacroDef mode"
      IO.eprintln s!"  Macro calls will be emitted as-is (may not compile without the macro definition)"
    -- Reclassify .skip entries that contain a needed macro definition
    let mut newEntries : Array CommandEntry := #[]
    for e in entries do
      if e.cls == .skip then
        let mut isMacroDef := false
        for pos in neededDeclPositions do
          if pos >= e.startPos && pos < e.endPos then
            isMacroDef := true
            break
        if isMacroDef then
          newEntries := newEntries.push { e with cls := .context }
        else
          newEntries := newEntries.push e
      else
        newEntries := newEntries.push e
    return newEntries
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
    (excludePrefixes : Array Name := #[])
    (cfg : Config := {}) : IO Unit := do
  -- Phase 1: Determine target module and its imports.
  -- Import the target module's direct imports — these transitively cover all
  -- dependencies. Only declarations from the target's own module (or other
  -- non-imported modules) need to be emitted.
  let targetModName := match env.getModuleIdxFor? targetName with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => rootPrefix
  -- Get all modules transitively imported by the target module's imports
  let targetModIdx := env.getModuleIdx? targetModName
  let importedModules : Std.HashSet Name := Id.run do
    let mut imported : Std.HashSet Name := {}
    -- All modules with index < target module's index are imported by it
    -- (since moduleNames is in dependency-first order)
    if let some tIdx := targetModIdx then
      for i in [:tIdx.toNat] do
        imported := imported.insert env.header.moduleNames[i]!
    imported
  IO.eprintln s!"Target module: {targetModName}"
  IO.eprintln s!"Imported modules: {importedModules.size}"

  -- Phase 1b: TFB names — keep all project-local declarations.
  -- For a TFB audit, we want to show everything the reader must trust.
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
  IO.eprintln s!"Emitting from {orderedModules.size} modules"

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
    let entries ← processFile source env tfbRangeMap filePath cfg
    allModules := allModules.push { modName, entries }

  -- Phase 4: Assemble from structured entries
  -- Collect universes, set_options, opens, and noncomputable from context commands.
  -- Items that appear in every (or nearly every) module with TFB decls get hoisted.
  let tfbModules := allModules.filter fun mc =>
    mc.entries.any fun e => match e.cls with | .tfbDecl _ => true | _ => false
  let numTFBModules := tfbModules.size
  let mut universeNames : Array String := #[]
  let mut setOptionCounts : Std.HashMap String Nat := {}
  let mut openCounts : Std.HashMap String Nat := {}
  let mut noncompCount : Nat := 0
  for mc in tfbModules do
    let mut seenOpts : Std.HashSet String := {}
    let mut seenOpens : Std.HashSet String := {}
    let mut hasNoncomp := false
    for e in mc.entries do
      match e.cls with
      | .context =>
        if e.kind == ``Parser.Command.universe then
          for word in e.src.splitOn " " do
            let w := word.trimAsciiEnd.toString
            if w != "universe" && !w.isEmpty && !universeNames.contains w then
              universeNames := universeNames.push w
        if e.kind == ``Parser.Command.set_option && !seenOpts.contains e.src then
          seenOpts := seenOpts.insert e.src
          setOptionCounts := setOptionCounts.insert e.src ((setOptionCounts.getD e.src 0) + 1)
        if e.kind == ``Parser.Command.open && !seenOpens.contains e.src then
          seenOpens := seenOpens.insert e.src
          openCounts := openCounts.insert e.src ((openCounts.getD e.src 0) + 1)
        if e.kind == ``Parser.Command.«section» && e.src.startsWith "noncomputable section" then
          hasNoncomp := true
      | _ => pure ()
    if hasNoncomp then noncompCount := noncompCount + 1
  -- Hoist set_options that appear in every TFB module
  let mut hoistedOpts : Array String := #[]
  for (src, count) in setOptionCounts do
    if count == numTFBModules then hoistedOpts := hoistedOpts.push src

  -- Emit header — import only external dependencies (e.g., Mathlib).
  -- Project-local modules are NOT imported; their TFB declarations are emitted.
  -- This ensures the standalone file shows all trusted declarations explicitly.
  let mut output := ""
  let mut emittedImports : Std.HashSet Name := {}
  -- Collect all imports from TFB modules that are external (not under rootPrefix)
  for modName in orderedModules do
    match env.getModuleIdx? modName with
    | some idx =>
      let imports := env.header.moduleData[idx.toNat]!.imports.map Import.module
      for imp in imports do
        if imp != `Init && !rootPrefix.isPrefixOf imp
          && !((`Informal).isPrefixOf imp) && !((`ProblemExtraction).isPrefixOf imp)
          && !emittedImports.contains imp then
          emittedImports := emittedImports.insert imp
          output := output ++ s!"import {imp}\n"
    | none => pure ()
  -- Also import direct imports of the target module that are external
  match env.getModuleIdx? targetModName with
  | some idx =>
    let imports := env.header.moduleData[idx.toNat]!.imports.map Import.module
    for imp in imports do
      if imp != `Init && !rootPrefix.isPrefixOf imp
          && !((`Informal).isPrefixOf imp) && !((`ProblemExtraction).isPrefixOf imp)
          && !emittedImports.contains imp then
        emittedImports := emittedImports.insert imp
        output := output ++ s!"import {imp}\n"
  | none => pure ()
  if emittedImports.isEmpty then
    output := output ++ "import Mathlib\n"
  output := output ++ "\n"
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

  -- Emit modules. Each module emits context + TFB declarations in source order.
  -- Hoisted set_options and universes are skipped. Spacing between sections.
  for mc in allModules do
    let hasTFB := mc.entries.any fun e => match e.cls with | .tfbDecl _ => true | _ => false
    if !hasTFB then continue
    let shortName := mc.modName.toString.drop (rootPrefix.toString.length + 1)
    output := output ++ s!"-- ═══ {shortName} ═══\n\n"
    let mut prevWasDecl := false
    for e in mc.entries do
      match e.cls with
      | .context =>
        if e.kind == ``Parser.Command.universe then continue
        if e.kind == ``Parser.Command.set_option && hoistedOpts.contains e.src then continue
        -- Add blank line before context that follows a declaration
        if prevWasDecl then output := output ++ "\n"
        output := output ++ e.src ++ "\n"
        prevWasDecl := false
      | .tfbDecl _ =>
        -- Add blank line before each declaration
        output := output ++ "\n"
        output := output ++ e.src ++ "\n"
        prevWasDecl := true
      | .skip => pure ()
    output := output ++ "\n"

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
