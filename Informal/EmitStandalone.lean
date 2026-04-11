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

Uses Lean's PrettyPrinter (`ppSignature`, `ppExpr`) to emit declarations from
the compiled environment — no source parsing needed. Declarations are ordered
by Kahn's topological sort using `usedConstants` for dependency edges.
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

-- ═══ Phase 2: Topological sort (Kahn's algorithm) ═══

/-- Compute direct dependencies of a declaration within a given set.
    Uses `usedConstants` (proof-irrelevant) and intersects with `relevantNames`. -/
def directDepsInSet (env : Environment) (name : Name) (relevantNames : Std.HashSet Name)
    : Array Name := Id.run do
  let some ci := env.find? name | return #[]
  let used := usedConstants ci (proofIrrelevant := true)
  let mut deps : Array Name := #[]
  for u in used.toArray do
    let resolved := resolveToUser env u
    if relevantNames.contains resolved && resolved != name then
      deps := deps.push resolved
  -- Deduplicate
  let deduped := deps.toList.eraseDups.toArray
  deduped

/-- Topological sort of a set of declaration names using Kahn's algorithm.
    Returns names in dependency order (dependencies first). -/
def topologicalSort (env : Environment) (names : Std.HashSet Name) : Array Name := Id.run do
  -- Build adjacency lists and in-degree counts
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
  -- Kahn's algorithm
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
  -- Append any remaining (cycles) at the end
  for n in nameArray do
    if !result.contains n then
      result := result.push n
  -- Reverse: Kahn's gives dependents-first, we want dependencies-first
  result.reverse

-- ═══ Phase 3: Declaration emission ═══

/-- Pretty-print a declaration as a standalone Lean statement using the environment.
    Structures/classes/inductives get their full definition.
    Theorems/defs/instances get `sorry` as body. -/
def ppDecl (env : Environment) (name : Name) : MetaM String := do
  let some ci := env.find? name | return s!"-- {name}: not found"
  let doc ← findDocString? env name
  let mut result := ""
  -- Docstring
  if let some d := doc then
    result := result ++ s!"/-- {d} -/\n"
  match ci with
  | .inductInfo iv =>
    -- Inductive type (including structures/classes)
    if isStructure env name then
      -- Use #print-style output for structures
      let sig : FormatWithInfos ← PrettyPrinter.ppSignature name
      result := result ++ s!"-- structure {name} (use #print for full definition)\n"
      result := result ++ s!"-- {sig.fmt}\n"
    else
      let sig : FormatWithInfos ← PrettyPrinter.ppSignature name
      result := result ++ s!"-- inductive {name}\n"
      result := result ++ s!"-- {sig.fmt}\n"
  | .thmInfo tv =>
    let sig : FormatWithInfos ← PrettyPrinter.ppSignature name
    result := result ++ s!"theorem {sig.fmt} := sorry"
  | .defnInfo dv =>
    let isAbbrev := (Lean.getReducibilityStatusCore env name) == .reducible
    let sig : FormatWithInfos ← PrettyPrinter.ppSignature name
    if isAbbrev then
      result := result ++ s!"abbrev {sig.fmt} := sorry"
    else
      result := result ++ s!"noncomputable def {sig.fmt} := sorry"
  | .axiomInfo _ =>
    let sig : FormatWithInfos ← PrettyPrinter.ppSignature name
    result := result ++ s!"axiom {sig.fmt}"
  | .opaqueInfo _ =>
    let sig : FormatWithInfos ← PrettyPrinter.ppSignature name
    result := result ++ s!"opaque {sig.fmt}"
  | _ =>
    result := result ++ s!"-- {name}: unsupported declaration kind"
  return result

/-- Main entry point: generate a standalone TFB file. -/
def emitStandalone (env : Environment) (rootPrefix : Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  -- Phase 1: Compute TFB names
  let tfbNames ← match computeTFBNames env rootPrefix targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"TFB: {tfbNames.size} declarations"

  -- Phase 2: Topological sort
  let sorted := topologicalSort env tfbNames
  IO.eprintln s!"Sorted {sorted.size} declarations"

  -- Phase 3: Emit each declaration
  let ctx : Core.Context := { fileName := "<emit>", fileMap := default }
  let state : Core.State := { env }
  let (declStrings, _) ← (do
    let mut results : Array String := #[]
    for name in sorted do
      let s ← (ppDecl env name).run'
      results := results.push s
    return results : CoreM _).toIO ctx state

  -- Phase 4: Assemble file
  let mut output := ""
  output := output ++ "import Mathlib\n\n"
  output := output ++ "/-! # Trusted Formalization Base\n"
  output := output ++ s!"{rootPrefix} — `{targetName}`\n"
  output := output ++ s!"Auto-generated — all proofs replaced with `sorry`.\n"
  output := output ++ s!"{tfbNames.size} declarations in dependency order.\n"
  output := output ++ "-/\n\n"
  output := output ++ "set_option autoImplicit false\n\n"
  output := output ++ s!"namespace {rootPrefix}\n\n"
  for s in declStrings do
    output := output ++ s ++ "\n\n"
  output := output ++ s!"end {rootPrefix}\n"
  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"

end Informal.EmitStandalone

/-- `#emit_standalone rootPrefix targetDecl "output.lean"` -/
elab "#emit_standalone" root:ident target:ident path:str : command => do
  let env ← getEnv
  Informal.EmitStandalone.emitStandalone env root.getId target.getId path.getString

end
