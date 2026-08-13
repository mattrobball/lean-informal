/-
Copyright (c) 2026 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard, Formalization
-/
module

public meta import Informal.EmitStandalone

/-!
# Boundary-aware standalone file generator

`EmitStandalone` draws its trust boundary with a single `rootPrefix`: modules
under it are inlined, everything else is imported and taken on faith. That is
the right boundary when a project is one package.

It is the wrong boundary when a project depends on another package that is
also ours. Then a single-prefix run silently imports in-house code as if it
were Mathlib, and the emitted file understates what a reader has to trust.

This module takes an `Array Name` of roots instead. A declaration is inlined
if it lives under ANY root, and imported otherwise. With every in-house
package named as a root, "imported" means exactly "external", which is the
boundary an audit actually wants.

The second difference is where source lives. `EmitStandalone` resolves a
module to `Foo/Bar.lean` relative to the working directory, which only holds
for the root project. Dependency packages sit under `.lake/packages/<pkg>/`,
so this module searches there too.

Everything else -- dependency collection, topological sort, InfoTree
re-elaboration, `sorry` injection, assembly -- is reused from
`EmitStandalone` unchanged.
-/

public meta section

open Lean Elab Command Meta Informal
open Informal.EmitStandalone

namespace Informal.EmitBoundary

/-- Is `mod` inside the trust boundary, i.e. under any of `roots`? -/
def inBoundary (roots : Array Name) (mod : Name) : Bool :=
  roots.any (·.isPrefixOf mod)

/-- The root that `mod` sits under, if any. Used to shorten section banners. -/
def matchingRoot? (roots : Array Name) (mod : Name) : Option Name :=
  roots.find? (·.isPrefixOf mod)

/-- Candidate source paths for a module, in search order: the root project
    first, then each package under `.lake/packages/`. -/
def sourceCandidates (modName : Name) : IO (Array System.FilePath) := do
  let rel := System.FilePath.mk (modName.toString.replace "." "/" ++ ".lean")
  let mut out : Array System.FilePath := #[rel]
  let pkgRoot : System.FilePath := ".lake/packages"
  if ← pkgRoot.pathExists then
    for entry in ← pkgRoot.readDir do
      out := out.push (entry.path / rel)
  return out

/-- Locate a module's source file. Returns `none` if nothing matches, which
    the caller reports rather than crashing -- a module whose source is not on
    disk cannot be inlined, and silently dropping it would understate the
    boundary. -/
def resolveSource (modName : Name) : IO (Option System.FilePath) := do
  for cand in ← sourceCandidates modName do
    if ← cand.pathExists then
      return some cand
  return none

/-- Names to inline: the target plus every dependency living under a root.

    Mirrors `EmitStandalone.computeTFBNames`, differing only in testing
    membership against an array of roots rather than one prefix. -/
def computeBoundaryNames (env : Environment) (roots : Array Name) (targetName : Name)
    (excludePrefixes : Array Name := #[])
    (importedEnv? : Option Environment := none) : Except String (Std.HashSet Name) := do
  let some ci := env.find? targetName
    | .error s!"Target declaration '{targetName}' not found in environment"
  let rawDeps := collectDeps env targetName ci (proofIrrelevant := true)
  let mut result : Std.HashSet Name := {}
  result := result.insert targetName
  for dep in rawDeps.toArray do
    let resolved := resolveToUser env dep
    if let some impEnv := importedEnv? then
      if impEnv.contains resolved then continue
    match env.getModuleIdxFor? resolved with
    | some idx =>
      let modName := env.header.moduleNames[idx.toNat]!
      if inBoundary roots modName
          && !excludePrefixes.any (·.isPrefixOf modName)
          && (classifyNonUser env resolved).isNone then
        result := result.insert resolved
    | none => pure ()
  if let some impEnv := importedEnv? then
    if impEnv.contains targetName then
      result := result.erase targetName
  return result

/-- Emit a standalone file whose trust boundary is `roots`.

    Declarations under any root are inlined with proofs replaced by `sorry`;
    everything else is imported. Name every in-house package as a root and the
    result imports only genuinely external code. -/
def emitBoundary (env : Environment) (roots : Array Name) (targetName : Name)
    (outputPath : System.FilePath)
    (excludePrefixes : Array Name := #[]) : IO Unit := do
  if roots.isEmpty then
    throw (IO.userError "emitBoundary: at least one --root is required")

  let targetModName := match env.getModuleIdxFor? targetName with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => roots[0]!
  IO.eprintln s!"Target module: {targetModName}"
  IO.eprintln s!"Boundary roots: {roots}"

  let names ← match computeBoundaryNames env roots targetName excludePrefixes with
    | .ok names => pure names
    | .error msg => throw (IO.userError msg)
  IO.eprintln s!"Inside boundary: {names.size} declarations"

  -- Module order follows env.header.moduleNames, which importModulesCore
  -- builds dependency-first, so it is already a valid topological order.
  let mut moduleSet : Std.HashSet Name := {}
  for name in names do
    if let some idx := env.getModuleIdxFor? name then
      moduleSet := moduleSet.insert env.header.moduleNames[idx.toNat]!
  let mut modIdxPairs : Array (Name × Nat) := #[]
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    if moduleSet.contains modName then
      modIdxPairs := modIdxPairs.push (modName, i)
  let orderedModules := (modIdxPairs.qsort fun a b => a.2 < b.2).map (·.1)
  IO.eprintln s!"Emitting from {orderedModules.size} modules"

  -- Per-module extraction, reusing EmitStandalone.processFile.
  let mut allModules : Array ModuleContent := #[]
  let mut unresolved : Array Name := #[]
  for modName in orderedModules do
    let some filePath ← resolveSource modName
      | unresolved := unresolved.push modName
        IO.eprintln s!"  !! {modName}: source not found, SKIPPED"
        continue
    let source ← IO.FS.readFile filePath
    let fileMap := FileMap.ofString source
    let mut rangeMap : Std.HashMap String.Pos.Raw Name := {}
    for name in names do
      if let some idx := env.getModuleIdxFor? name then
        if env.header.moduleNames[idx.toNat]! == modName then
          if let some ranges := findDeclRanges? env name then
            rangeMap := rangeMap.insert (fileMap.ofPosition ranges.range.pos) name
    IO.eprintln s!"  {filePath} ({rangeMap.size} decls)"
    let entries ← processFile source env rangeMap filePath.toString
    allModules := allModules.push { modName, entries := stripEmptySections entries }

  -- Header: import only what is outside the boundary.
  let mut output := ""
  let mut emittedImports : Std.HashSet Name := {}
  let mut importSources : Array Name := orderedModules.push targetModName
  for modName in importSources do
    match env.getModuleIdx? modName with
    | some idx =>
      for imp in env.header.moduleData[idx.toNat]!.imports.map Import.module do
        if imp != `Init && !inBoundary roots imp
            && !((`Informal).isPrefixOf imp) && !((`ProblemExtraction).isPrefixOf imp)
            && !emittedImports.contains imp then
          emittedImports := emittedImports.insert imp
          output := output ++ s!"import {imp}\n"
    | none => pure ()
  if emittedImports.isEmpty then
    output := output ++ "import Mathlib\n"
  output := output ++ "\n"

  let mut universeNames : Array String := #[]
  for mc in allModules do
    for e in mc.entries do
      if e.cls == .context && e.kind == ``Parser.Command.universe then
        for word in e.src.splitOn " " do
          let w := word.trimAsciiEnd.toString
          if w != "universe" && !w.isEmpty && !universeNames.contains w then
            universeNames := universeNames.push w

  output := output ++ "/-! # Trusted base\n\n"
  output := output ++ s!"Target: `{targetName}`\n\n"
  output := output ++ s!"Boundary: {", ".intercalate (roots.toList.map toString)}\n\n"
  output := output ++ s!"{names.size} declarations from {orderedModules.size} modules, \
    inlined in dependency order with every proof replaced by `sorry`. Imports above \
    are outside the boundary and are trusted as given.\n"
  unless unresolved.isEmpty do
    output := output ++ s!"\nWARNING: source not found for \
      {", ".intercalate (unresolved.toList.map toString)} -- \
      these are INSIDE the boundary but could not be inlined.\n"
  output := output ++ "-/\n\n"
  unless universeNames.isEmpty do
    output := output ++ "universe " ++ " ".intercalate universeNames.toList ++ "\n\n"

  for mc in allModules do
    let hasDecl := mc.entries.any fun e => match e.cls with | .tfbDecl _ => true | _ => false
    if !hasDecl then continue
    let shortName := match matchingRoot? roots mc.modName with
      | some r => mc.modName.toString.drop (r.toString.length + 1)
      | none => mc.modName.toString
    output := output ++ s!"-- ═══ {shortName} ═══\n\n"
    let mut prevWasDecl := false
    for e in mc.entries do
      match e.cls with
      | .context =>
        if e.kind == ``Parser.Command.universe then continue
        if e.kind == ``Parser.Command.set_option then continue
        if prevWasDecl then output := output ++ "\n"
        output := output ++ e.src ++ "\n"
        prevWasDecl := false
      | .tfbDecl _ =>
        output := output ++ "\n"
        output := output ++ e.src ++ "\n"
        prevWasDecl := true
      | .skip => pure ()
    output := output ++ "\n"

  -- These attributes would require importing Informal, which the emitted file
  -- does not do.
  let filtered := output.splitOn "\n" |>.filter fun line =>
    let t := line.trimAsciiStart.toString
    !(t.startsWith "@[informal " || t.startsWith "@[expose]")
  output := ("\n".intercalate filtered).trimAsciiEnd.toString ++ "\n"

  IO.FS.writeFile outputPath output
  IO.eprintln s!"Wrote {outputPath}"
  unless unresolved.isEmpty do
    IO.eprintln s!"WARNING: {unresolved.size} in-boundary module(s) had no source on disk"

end Informal.EmitBoundary

end
