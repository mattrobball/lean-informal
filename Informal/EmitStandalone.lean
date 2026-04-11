/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard, Formalization
-/
module

public meta import Informal.Deps
public meta import Informal.Classify
public meta import Informal.Extract
public meta import Lean

/-!
# Standalone TFB file generator

Given a compiled Lean environment and a target declaration name, generates a
single standalone `.lean` file containing all transitive type-level dependencies
(the Trusted Formalization Base) with proofs replaced by `sorry`.

No annotations or special markup required in the source repo.

Follows the compfiles (`dwrensha/compfiles`) pattern of working with original
source text and applying targeted replacements, but discovers TFB declarations
automatically via `collectDeps`.
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
  | some (.defnInfo di) =>
    -- Abbrevs should keep their bodies (needed for reducibility)
    match Lean.isReducible env name with
    | true => false  -- it's an abbrev
    | false => true
  | some (.opaqueInfo _) => false  -- already opaque
  | _ => false

/-- Strip the proof body from a declaration's source text, replacing it with `:= sorry`.
    Uses bracket-balanced splitting to find the top-level `:=` or `where`. -/
def sorryifySource (source : String) : String := Id.run do
  -- Find the top-level `:=` (not inside brackets)
  let chars := source.toList
  let mut round := 0
  let mut curly := 0
  let mut square := 0
  let mut i := 0
  let mut foundAssign := false
  let mut assignIdx := 0

  -- Also track `where` at top level
  let mut foundWhere := false
  let mut whereIdx := 0

  while i < chars.length do
    let c := chars[i]!
    match c with
    | '(' => round := round + 1
    | ')' => round := round - 1
    | '{' => curly := curly + 1
    | '}' => curly := curly - 1
    | '[' => square := square + 1
    | ']' => square := square - 1
    | ':' =>
      if round == 0 && curly == 0 && square == 0 then
        if i + 1 < chars.length && chars[i + 1]! == '=' then
          foundAssign := true
          assignIdx := i
    | 'w' =>
      if round == 0 && curly == 0 && square == 0 then
        -- Check for "where" keyword
        let rest := (source.drop i).take 5
        if rest == "where" then
          -- Make sure it's not part of a larger word
          let prevOk := i == 0 || (chars[i-1]!).isWhitespace
          let nextOk := i + 5 >= chars.length || (chars[i+5]!).isWhitespace
          if prevOk && nextOk then
            foundWhere := true
            whereIdx := i
    | _ => pure ()
    i := i + 1

  if foundAssign then
    -- Check if `:=` comes before `where`, or if no `where`
    let useAssign := !foundWhere || assignIdx < whereIdx
    if useAssign then
      return (source.take assignIdx).trimRight ++ " := sorry"
  if foundWhere then
    return (source.take whereIdx).trimRight ++ " := sorry"

  -- Fallback: couldn't find assignment, return as-is
  return source

-- ═══ Phase 3: File assembly ═══

/-- Extract the content of a source file relevant to TFB declarations.
    Reads the file, identifies TFB declaration ranges, extracts context lines
    before the first TFB declaration, and sorry's proof bodies.

    Returns the processed content for this module, or none if no TFB content. -/
def processModule (env : Environment) (modName : Name) (rootPrefix : Name)
    (tfbNames : Std.HashSet Name) (declNames : Array Name) : IO (Option String) := do
  let sourcePath := modName.toString.replace "." "/" ++ ".lean"
  let source ← IO.FS.readFile sourcePath
  let lines := (source.splitOn "\n").toArray

  -- Get declaration ranges for TFB names, sorted by start line
  let mut rangeEntries : Array (Name × Nat × Nat) := #[]
  for name in declNames do
    if let some ranges := (← findDeclarationRanges? name) then
      rangeEntries := rangeEntries.push (name, ranges.range.pos.line, ranges.range.endPos.line)
  let rangeEntries := rangeEntries.qsort fun a b => a.2.1 < b.2.1

  if rangeEntries.isEmpty then return none

  let earliestLine := rangeEntries.foldl (fun acc (_, l, _) => min acc l) (lines.size + 1)

  -- Build output
  let shortName := modName.toString.stripPrefix (rootPrefix.toString ++ ".")
  let mut out := s!"\n-- ═══ {shortName} ═══\n\n"

  -- 1. Context lines: everything before the first TFB declaration that isn't an import/module
  for i in [:earliestLine - 1] do
    let line := lines[i]!
    let trimmed := line.trimLeft
    -- Skip import and module lines
    if trimmed.startsWith "import " || trimmed.startsWith "public import " ||
       trimmed.startsWith "meta import " || trimmed.startsWith "public meta import " ||
       (trimmed == "module") then
      continue
    -- Skip module docstrings (/-! ... -/) — they reference project-specific content
    -- Keep everything else: namespace, open, variable, section, set_option, universe,
    -- noncomputable, attributes, comments, blank lines, @[expose]
    out := out ++ line ++ "\n"

  -- 2. TFB declarations with sorry injection
  for (name, startLine, endLine) in rangeEntries do
    -- Extract the declaration source
    let declLines := lines[startLine - 1 : endLine]
    let declSource := "\n".intercalate declLines.toList

    -- Check if we need to sorry the body
    if needsSorry env name then
      out := out ++ sorryifySource declSource ++ "\n\n"
    else
      out := out ++ declSource ++ "\n\n"

  -- 3. Closing `end` statements: scan from after last TFB decl to EOF
  let lastEnd := rangeEntries.foldl (fun acc (_, _, el) => max acc el) 0
  for i in [lastEnd : lines.size] do
    let line := lines[i]!
    let trimmed := line.trimLeft
    if trimmed.startsWith "end " || trimmed == "end" then
      out := out ++ line ++ "\n"

  return some out

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
    IO.eprintln s!"  Processing {modName}"
    let some declNames := moduleMap[modName]? | continue
    if let some content ← processModule env modName rootPrefix tfbNames declNames then
      fileContents := fileContents.push content

  -- Phase 4: Assemble final file
  let mut output := ""
  output := output ++ "/-! # Trusted Formalization Base\n"
  output := output ++ s!"{rootPrefix} — `{targetName}`\n"
  output := output ++ "Auto-generated — all proofs replaced with `sorry`.\n"
  output := output ++ "-/\n"
  output := output ++ "import Mathlib\n"
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
