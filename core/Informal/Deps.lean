/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Lean

/-!
# Transitive dependency collection

Computes the transitive closure of project-local constants referenced by a
declaration. Returns a raw `NameSet` — no resolution, no hashing.

The `proofIrrelevant` flag controls whether theorem values are followed:
- `true`: skip theorem bodies (only follow their types)
- `false`: follow everything (for axiom-style audits)
-/

public meta section

open Lean

namespace Informal

/-- One-level used constants for a `ConstantInfo`.
When `proofIrrelevant` is true, skips theorem values.
Exhaustive on all `ConstantInfo` constructors. -/
def usedConstants (ci : ConstantInfo) (proofIrrelevant : Bool := true) : NameSet :=
  ci.type.getUsedConstantsAsSet ++ match ci with
  | .thmInfo v    => if proofIrrelevant then {} else v.value.getUsedConstantsAsSet
  | .defnInfo v   => v.value.getUsedConstantsAsSet
  | .opaqueInfo v => v.value.getUsedConstantsAsSet
  | .inductInfo v => .ofList v.ctors
  | .ctorInfo v   => ({} : NameSet).insert v.name
  | .recInfo v    => .ofList v.all
  | .axiomInfo _  => {}
  | .quotInfo _   => {}

private structure CollectState where
  visited : NameSet := {}
  deps : NameSet := {}

private abbrev CollectM := ReaderT (Environment × (Name → Bool) × Bool) (StateM CollectState)

/-- Recursively collect the transitive closure of dependencies, recording the
constants for which `inScope` holds.

`inScope` is the single filter: a constant is recorded iff `inScope c`. The default
records project-local constants. Recursion follows the same predicate, with one fixed
exception — we always finish walking the *current* compilation unit (constants with no
module index yet, e.g. same-file helpers at `afterCompilation` time). That exception is
load-bearing: a project-local dependency reached only through a same-file helper
(`D → H → J`) would otherwise be dropped. Everything else out of scope — notably
upstream packages like mathlib — is pruned, which is both sound (an upstream constant
cannot reference a project-local one) and the whole speedup: it stops
`proofIrrelevant := false` from materializing a large fraction of mathlib's proof
terms. -/
private partial def collect (c : Name) : CollectM Unit := do
  let s ← get
  if s.visited.contains c then return
  modify fun s => { s with visited := s.visited.insert c }
  let (env, inScope, pi) ← read
  let some ci := env.find? c | return
  let keep := inScope c
  if keep then
    modify fun s => { s with deps := s.deps.insert c }
  if keep || (env.getModuleIdxFor? c).isNone then
    (usedConstants ci pi).forM collect

/-- Compute the transitive closure of dependencies for a declaration, recording the
constants for which `inScope` holds.

`inScope?` defaults to "project-local" (same module root as `name`) — returning every
project-local constant in the dependency graph, exactly as before, but with the walk
pruned at the upstream-package boundary (a sound speedup; see `collect`). Pass an
explicit predicate to collect against a different boundary (a single module root, a
namespace allow-list, …).

When `proofIrrelevant` is true (default), theorem values are skipped but their types
are still followed. -/
def collectDeps (env : Environment) (name : Name) (ci : ConstantInfo)
    (proofIrrelevant : Bool := true)
    (inScope? : Option (Name → Bool) := none) : NameSet := Id.run do
  let projectRoot := match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!.getRoot
    | none => env.mainModule.getRoot
  let scope : Name → Bool := inScope?.getD fun c =>
    match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx.toNat]!.getRoot == projectRoot
    | none => false
  let mut s : CollectState := {}
  s := { s with visited := s.visited.insert name }
  (_, s) := ((usedConstants ci proofIrrelevant).forM collect
    |>.run (env, scope, proofIrrelevant)).run s
  s.deps

end Informal

end
