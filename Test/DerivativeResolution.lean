/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
import Informal

/-!
# Test suite for dependency tracking

Tests the refactored `Informal.Attr` logic:
- `usedConstants`: proof-irrelevant one-level constant extraction
- `isUserDecl`: structural filtering (no name-pattern heuristics)
- `resolveToUser`: derivative → parent resolution
- `collectDep` / `computeDepHashes`: transitive dependency walk

Each test uses `#eval` with a guard that throws on failure.
-/

open Lean Informal

-- ============================================================
-- Test declarations: cover every ConstantInfo variant
-- ============================================================

inductive Color where | red | green | blue

inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

structure Point where
  x : Nat
  y : Nat

class HasSize (α : Type) where
  size : α → Nat

def matchFunc : Nat → String
  | 0 => "zero"
  | n + 1 => s!"succ {n}"

def matchFunc2 : Bool → Nat → Nat
  | true, n => n + 1
  | false, n => n

opaque opaqueFunc : Nat

theorem trivialThm : 1 + 1 = 2 := rfl

abbrev myAbbrev := Point

-- A def that directly references a match auxiliary (adversarial case)
def sneaky (n : Nat) : String :=
  matchFunc.match_1 (fun _ => String) n (fun _ => "zero") (fun k => s!"succ {k}")

-- ============================================================
-- Test 1: usedConstants skips theorem values
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv

  -- theorem: only type constants, not proof constants
  let some thmCi := env.find? `trivialThm | throwError "trivialThm not found"
  let piConsts := usedConstants thmCi
  let fullConsts := thmCi.getUsedConstantsAsSet
  -- PI should be a subset of full (skips proof body)
  unless piConsts.size ≤ fullConsts.size do
    throwError "usedConstants should return ≤ constants for a theorem"
  -- PI should only contain type constants
  let typeConsts := thmCi.type.getUsedConstantsAsSet
  unless piConsts.size == typeConsts.size && piConsts.toArray.all typeConsts.contains do
    throwError "usedConstants for theorem should equal type-only constants"

  -- def with match: PI should include value constants
  let some defCi := env.find? `matchFunc | throwError "matchFunc not found"
  let piDef := usedConstants defCi
  let typeDef := defCi.type.getUsedConstantsAsSet
  unless piDef.size > typeDef.size do
    throwError "usedConstants for def should include value constants beyond type"

  -- inductive: PI should include constructors
  let some indCi := env.find? `Color | throwError "Color not found"
  let piInd := usedConstants indCi
  unless piInd.contains `Color.red do
    throwError "usedConstants for inductive should include constructor names"

  -- opaque: has no accessible value, but usedConstants still returns type constants
  let some opCi := env.find? `opaqueFunc | throwError "opaqueFunc not found"
  let piOp := usedConstants opCi
  -- At minimum, type constants should be present
  let typeOp := opCi.type.getUsedConstantsAsSet
  unless typeOp.toArray.all piOp.contains do
    throwError "usedConstants for opaque should contain all type constants"

  IO.println "PASS: usedConstants"

-- ============================================================
-- Test 2: isUserDecl structural filtering
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv

  -- User-facing declarations should pass
  for n in #[`Color, `Tree, `Point, `HasSize, `matchFunc, `trivialThm, `opaqueFunc] do
    unless isUserDecl env n do
      throwError s!"isUserDecl should accept {n}"

  -- Constructors should be rejected
  for n in #[`Color.red, `Color.green, `Tree.leaf, `Tree.node, `Point.mk] do
    if isUserDecl env n then
      throwError s!"isUserDecl should reject constructor {n}"

  -- Recursors should be rejected
  for n in #[`Color.rec, `Tree.rec, `Point.rec] do
    if isUserDecl env n then
      throwError s!"isUserDecl should reject recursor {n}"

  -- Aux recursors should be rejected
  for n in #[`Color.casesOn, `Color.recOn, `Tree.casesOn, `Tree.brecOn, `Tree.below] do
    if isUserDecl env n then
      throwError s!"isUserDecl should reject aux recursor {n}"

  -- noConfusion should be rejected
  for n in #[`Color.noConfusion, `Tree.noConfusion] do
    if isUserDecl env n then
      throwError s!"isUserDecl should reject noConfusion {n}"

  -- Projections should be rejected
  for n in #[`Point.x, `Point.y, `HasSize.size] do
    if isUserDecl env n then
      throwError s!"isUserDecl should reject projection {n}"

  IO.println "PASS: isUserDecl"

-- ============================================================
-- Test 3: resolveToUser maps derivatives to parents
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv

  -- User-facing names should resolve to themselves
  for n in #[`Color, `Point, `matchFunc] do
    let r := resolveToUser env n
    unless r == n do
      throwError s!"resolveToUser should map {n} to itself, got {r}"

  -- Constructors resolve to parent inductive
  for (d, p) in #[(`Color.red, `Color), (`Tree.leaf, `Tree), (`Point.mk, `Point)] do
    let r := resolveToUser env d
    unless r == p do
      throwError s!"resolveToUser should map {d} to {p}, got {r}"

  -- Aux recursors resolve to parent
  for (d, p) in #[(`Color.casesOn, `Color), (`Tree.brecOn, `Tree), (`Tree.below, `Tree)] do
    let r := resolveToUser env d
    unless r == p do
      throwError s!"resolveToUser should map {d} to {p}, got {r}"

  -- noConfusion resolves to parent
  let r := resolveToUser env `Color.noConfusion
  unless r == `Color do
    throwError s!"resolveToUser should map Color.noConfusion to Color, got {r}"

  -- Projections resolve to parent structure
  for (d, p) in #[(`Point.x, `Point), (`Point.y, `Point)] do
    let r := resolveToUser env d
    unless r == p do
      throwError s!"resolveToUser should map {d} to {p}, got {r}"

  -- match_ auxiliaries resolve to parent def
  let derivs := env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == `matchFunc && n != `matchFunc then acc.push n else acc
  for d in derivs do
    let r := resolveToUser env d
    unless r == `matchFunc do
      throwError s!"resolveToUser should map {d} to matchFunc, got {r}"

  IO.println "PASS: resolveToUser"

-- ============================================================
-- Test 4: match_ auxiliary doesn't reference its parent
--         (validates the adversarial scenario that motivates resolveToUser)
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv
  let derivs := env.constants.fold (init := #[]) fun acc n _ =>
    if n.getPrefix == `matchFunc && n != `matchFunc && n.isInternalDetail then
      acc.push n
    else acc
  if derivs.isEmpty then
    throwError "matchFunc should have at least one match_ derivative"
  for d in derivs do
    let some ci := env.find? d | throwError s!"{d} not found"
    let used := ci.getUsedConstantsAsSet
    if used.contains `matchFunc then
      throwError s!"{d} references matchFunc — adversarial test premise is wrong"
    -- But getPrefix resolves it
    unless d.getPrefix == `matchFunc do
      throwError s!"{d}.getPrefix should be matchFunc"

  IO.println "PASS: match_ adversarial scenario"

-- ============================================================
-- Test 5: sneaky (direct match_ reference) resolves to matchFunc
--         via usedConstants + resolveToUser
--         (computeDepHashes can't see same-file declarations as project-local,
--          so we test the resolution components directly)
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv
  let some ci := env.find? `sneaky | throwError "sneaky not found"
  let used := usedConstants ci
  -- sneaky's used constants should include matchFunc.match_1
  let matchAuxes := used.toArray.filter (·.getPrefix == `matchFunc)
  unless !matchAuxes.isEmpty do
    throwError s!"sneaky should reference a matchFunc.* auxiliary"
  -- Each match auxiliary should resolve to matchFunc
  for aux in matchAuxes do
    let resolved := resolveToUser env aux
    unless resolved == `matchFunc do
      throwError s!"{aux} should resolve to matchFunc, got {resolved}"

  IO.println "PASS: sneaky → matchFunc resolution"

-- ============================================================
-- Test 6: computeHash exhaustive constructor coverage
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv
  -- Every declaration kind should produce a nonzero hash
  let decls : Array Name := #[`Color, `Tree, `Point, `matchFunc, `trivialThm,
    `opaqueFunc, `Color.red, `Color.rec]
  for n in decls do
    let some ci := env.find? n | throwError s!"{n} not found"
    let h := computeHash env n ci
    -- Hash should be deterministic (same input → same output)
    let h2 := computeHash env n ci
    unless h == h2 do
      throwError s!"computeHash not deterministic for {n}"

  -- Theorem hash should depend only on type, not proof
  let some thmCi := env.find? `trivialThm | throwError "trivialThm not found"
  let thmHash := computeHash env `trivialThm thmCi
  let typeOnlyHash := thmCi.type.hash
  unless thmHash == typeOnlyHash do
    throwError "theorem hash should equal type-only hash"

  -- Def hash should differ from type-only hash (includes value)
  let some defCi := env.find? `matchFunc | throwError "matchFunc not found"
  let defHash := computeHash env `matchFunc defCi
  let defTypeHash := defCi.type.hash
  unless defHash != defTypeHash do
    throwError "def hash should differ from type-only hash"

  IO.println "PASS: computeHash"

-- ============================================================
-- Test 7: computeDepHashes produces consistent, sorted results
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv
  let some ci := env.find? `sneaky | throwError "sneaky not found"
  let deps1 := computeDepHashes env `sneaky ci
  let deps2 := computeDepHashes env `sneaky ci

  -- Deterministic
  unless deps1.size == deps2.size do
    throwError "computeDepHashes not deterministic (size)"
  for i in [:deps1.size] do
    unless deps1[i]! == deps2[i]! do
      throwError s!"computeDepHashes not deterministic at index {i}"

  -- Sorted by name
  for i in [:deps1.size - 1] do
    unless Name.lt deps1[i]!.1 deps1[i+1]!.1 do
      throwError s!"computeDepHashes not sorted at index {i}"

  -- Should not include the declaration itself
  unless !deps1.any (·.1 == `sneaky) do
    throwError "computeDepHashes should not include the declaration itself"

  IO.println "PASS: computeDepHashes"

-- ============================================================
-- Test 8: theorem deps come from type only
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv
  let some ci := env.find? `trivialThm | throwError "trivialThm not found"
  let deps := computeDepHashes env `trivialThm ci
  -- trivialThm : 1 + 1 = 2 := rfl
  -- Deps should come from the type (Eq, HAdd, Nat, etc.) not the proof (Eq.refl)
  -- There should be no project-local deps since the type only uses builtins
  unless deps.isEmpty do
    throwError s!"trivialThm should have no project-local deps, got {deps.size}"

  IO.println "PASS: theorem type-only deps"

-- ============================================================
-- Test 9: every derivative of test declarations resolves
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv
  let parents := #[`Color, `Tree, `Point, `HasSize, `matchFunc, `matchFunc2]
  let mut failures : Array String := #[]

  for parent in parents do
    let derivs := env.constants.fold (init := #[]) fun acc n _ =>
      if n != parent && n.getPrefix == parent then acc.push n else acc
    for d in derivs do
      let resolved := resolveToUser env d
      let isProof := match env.find? d with | some (.thmInfo _) => true | _ => false
      -- Every non-proof derivative should resolve to the parent
      if !isProof && resolved != parent then
        failures := failures.push s!"{d} resolved to {resolved}, expected {parent}"

  unless failures.isEmpty do
    let msg := String.intercalate "\n  " failures.toList
    throwError s!"resolveToUser failures:\n  {msg}"

  IO.println "PASS: all derivatives resolve to parent"

-- ============================================================
-- Test 10: noConfusionType and ctorIdx (names not caught by core API)
--          are still handled by resolveToUser
-- ============================================================

#eval show MetaM Unit from do
  let env ← getEnv
  -- These are data-carrying defs not caught by isAuxRecursor/isNoConfusion/projection
  for (d, p) in #[(`Color.noConfusionType, `Color), (`Color.ctorIdx, `Color),
                   (`Tree.noConfusionType, `Tree), (`Tree.ctorIdx, `Tree)] do
    unless (env.find? d).isSome do continue  -- skip if not generated
    -- isUserDecl should reject them (they fail isInternal or structural checks)
    -- OR resolveToUser should map them to parent
    let resolved := resolveToUser env d
    unless resolved == p do
      throwError s!"{d} should resolve to {p}, got {resolved}"

  IO.println "PASS: noConfusionType/ctorIdx resolution"
