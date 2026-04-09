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

private abbrev CollectM := ReaderT (Environment × Name × Bool) (StateM CollectState)

/-- Recursively collect the transitive closure of dependencies.
Records every project-local constant encountered — no filtering,
no derivative resolution. -/
private partial def collect (c : Name) : CollectM Unit := do
  let s ← get
  if s.visited.contains c then return
  modify fun s => { s with visited := s.visited.insert c }
  let (env, projectRoot, pi) ← read
  let some ci := env.find? c | return
  match env.getModuleIdxFor? c with
  | some idx =>
    if env.header.moduleNames[idx.toNat]!.getRoot == projectRoot then
      modify fun s => { s with deps := s.deps.insert c }
  | none => pure ()
  (usedConstants ci pi).forM collect

/-- Compute the transitive closure of dependencies for a declaration.
Returns every project-local constant in the dependency graph.

When `proofIrrelevant` is true (default), theorem values are skipped
but their types are still followed. -/
def collectDeps (env : Environment) (name : Name) (ci : ConstantInfo)
    (proofIrrelevant : Bool := true) : NameSet := Id.run do
  let projectRoot := match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!.getRoot
    | none => env.mainModule.getRoot
  let mut s : CollectState := {}
  s := { s with visited := s.visited.insert name }
  (_, s) := ((usedConstants ci proofIrrelevant).forM collect
    |>.run (env, projectRoot, proofIrrelevant)).run s
  s.deps

end Informal

end
