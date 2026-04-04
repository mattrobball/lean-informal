/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Lean.Elab.Command

/-!
# Informal paper reference attribute

The `@[informal]` attribute tags a formal Lean declaration with a reference
to a statement in a mathematical paper or text. It stores the reference in a
persistent environment extension, making it available for documentation
generation, drift detection, and cross-referencing tooling.

At application time, the attribute records a snapshot of the declaration's
content hash and the hashes of its dependencies, enabling `#check_informal`
to detect when a tagged declaration or its dependencies have changed.

## Usage

```
@[informal "Definition 3.3"]
structure Slicing where ...

@[informal "Theorem 7.1" "deformation of stability conditions"]
theorem deformed : ... := ...
```

The first argument is the paper reference (free-form string).
The optional second argument is a brief comment or gloss.

Multiple declarations may reference the same paper statement:

```
@[informal "Proposition 5.3"]
theorem heartEquiv_forward ...

@[informal "Proposition 5.3"]
theorem heartEquiv_reverse ...
```
-/

public meta section

open Lean Elab

namespace Informal

/-- An informal paper reference entry stored in the environment.
Includes a snapshot of the declaration's content hash and dependency hashes
at the time the tag was applied, for drift detection. -/
structure Entry where
  /-- The Lean declaration name. -/
  declName : Name
  /-- The paper reference, e.g., "Definition 5.1", "Theorem 7.1". -/
  paperRef : String
  /-- Optional comment or gloss. -/
  comment : String := ""
  /-- Hash of the declaration's type (and body for data-carrying declarations)
      at the time the tag was applied. -/
  contentHash : UInt64 := 0
  /-- Hashes of the declaration's dependencies at the time the tag was applied.
      Each pair is `(depName, depHash)`. Only project-local dependencies are
      tracked (Mathlib/Lean builtins are skipped). -/
  depHashes : Array (Name × UInt64) := #[]
  deriving BEq, Hashable, Inhabited

/-- Persistent environment extension storing all informal entries. -/
initialize informalExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
    addEntryFn := fun arr e => arr.push e
  }

/-- Retrieve all informal entries from the environment. -/
def getEntries (env : Environment) : Array Entry :=
  informalExt.getState env

/-- Retrieve entries for a specific paper reference. -/
def getEntriesFor (env : Environment) (paperRef : String) : Array Entry :=
  (getEntries env).filter (·.paperRef == paperRef)

/-- Is this declaration proof-irrelevant (only type matters for hash)? -/
def isProofIrrelevant (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ => true
  | _ => false

/-- Compute a content hash for a declaration using `Expr.hash` (context-independent).
For proof-irrelevant declarations (theorems), hashes only the type.
For data-carrying declarations (defs, structures, etc.), hashes type + body/fields. -/
def computeHash (env : Environment) (name : Name) (ci : ConstantInfo) : UInt64 := Id.run do
  if isProofIrrelevant ci then
    return ci.type.hash
  let mut h := ci.type.hash
  match ci with
  | .defnInfo di => h := mixHash h di.value.hash
  | .opaqueInfo oi => h := mixHash h oi.value.hash
  | _ => ()
  if let some sinfo := getStructureInfo? env name then
    for field in sinfo.fieldNames do
      if let some projInfo := env.find? (name ++ field) then
        h := mixHash h projInfo.type.hash
  if let .inductInfo ii := ci then
    for ctorName in ii.ctors do
      if let some ctorInfo := env.find? ctorName then
        h := mixHash h ctorInfo.type.hash
  return h

/-- Is this a name component that indicates auto-generated code? -/
def isAuxComponent (s : String) : Bool :=
  s.startsWith "_" || s.startsWith "match_" || s.startsWith "proof_"

/-- Is this name auto-generated (internal, projection, recursor, etc.)? -/
partial def isAutoGenName : Name → Bool
  | .anonymous => false
  | .num p _ => isAutoGenName p
  | .str p s =>
      isAuxComponent s
      || s ∈ ["brecOn", "below", "casesOn", "noConfusion", "noConfusionType",
              "recOn", "rec", "ind", "mk", "sizeOf_spec", "inject", "injEq",
              "ctorIdx", "ext_iff", "congr_simp"]
      || (s.startsWith "eq_" && (s.drop 3).toString.all Char.isDigit)
      || isAutoGenName p

/-- Should this constant be tracked as a dependency? Filters out auto-generated
declarations, projections, constructors, recursors, etc. -/
def isUserDecl (env : Environment) (dep : Name) : Bool :=
  if isAutoGenName dep || dep.isInternal || dep.isImplementationDetail then false
  else if env.getProjectionFnInfo? dep |>.isSome then false
  else if isAuxRecursor env dep || isNoConfusion env dep then false
  else match env.find? dep with
    | some (.ctorInfo _) | some (.recInfo _) | some (.quotInfo _) => false
    | _ => true

/-- Collect the direct dependencies of a declaration and compute their hashes.
Only includes project-local, user-written constants (skips Mathlib/Lean builtins,
projections, recursors, constructors, and other auto-generated declarations). -/
def computeDepHashes (env : Environment) (name : Name) (ci : ConstantInfo)
    : Array (Name × UInt64) := Id.run do
  -- Collect constants from type
  let mut depSet : NameSet := {}
  for c in ci.type.getUsedConstants do
    if c != name then depSet := depSet.insert c
  -- For data-carrying declarations, also collect from value/constructors
  if !isProofIrrelevant ci then
    match ci with
    | .defnInfo di =>
      for c in di.value.getUsedConstants do
        if c != name then depSet := depSet.insert c
    | .opaqueInfo oi =>
      for c in oi.value.getUsedConstants do
        if c != name then depSet := depSet.insert c
    | .inductInfo ii =>
      for ctorName in ii.ctors do
        if let some ctorCi := env.find? ctorName then
          for c in ctorCi.type.getUsedConstants do
            if c != name then depSet := depSet.insert c
    | _ => ()
  -- Determine project root for filtering.
  -- At attribute application time, the current module may not be in header.moduleNames.
  let declRoot := match env.getModuleIdxFor? name with
    | some idx => env.header.moduleNames[idx.toNat]!.getRoot
    | none => env.mainModule.getRoot
  -- Filter to project-local, user-written constants
  let mut result : Array (Name × UInt64) := #[]
  for dep in depSet.toArray.qsort Name.lt do
    unless isUserDecl env dep do continue
    let some modIdx := env.getModuleIdxFor? dep | continue
    let modName := env.header.moduleNames[modIdx.toNat]!
    unless declRoot == modName.getRoot do continue
    let some depCi := env.find? dep | continue
    let h := computeHash env dep depCi
    result := result.push (dep, h)
  return result

/-- The `@[informal]` attribute syntax. -/
syntax (name := informal) "informal" str (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `informal
  descr := "Tag a declaration with a paper reference and record a content snapshot."
  add := fun decl stx _attrKind => do
    let (paperRef, comment) ← match stx with
      | `(attr| informal $ref $[$cmt]?) =>
        pure (ref.getString, (cmt.map (·.getString)).getD "")
      | _ => throwUnsupportedSyntax
    let env ← getEnv
    let some ci := env.find? decl
      | throwError "declaration '{decl}' not found in environment"
    let contentHash := computeHash env decl ci
    let depHashes := computeDepHashes env decl ci
    modifyEnv (informalExt.addEntry · {
      declName := decl
      paperRef
      comment
      contentHash
      depHashes
    })
  applicationTime := .afterCompilation
}

end Informal

end
