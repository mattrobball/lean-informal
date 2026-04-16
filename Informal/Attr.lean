/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Lean.Elab.Command
public meta import Informal.Classify
public meta import Informal.Deps

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
An optional trailing `complete` or `incomplete` keyword sets the
formalization status; omitting it defaults to `incomplete`.

```
@[informal "Theorem 7.1" complete]
theorem deformed : ... := ...

@[informal "Proposition 5.3" "forward direction only"]
theorem heartEquiv_forward ...
```

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

/-- Formalization status of a declaration relative to its paper statement. -/
inductive DeclStatus where
  | complete
  | incomplete
  deriving BEq, Repr, Inhabited, Hashable

instance : ToString DeclStatus where
  toString | .complete => "complete" | .incomplete => "incomplete"

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
  /-- Formalization status: `incomplete` (default) or `complete`. -/
  status : DeclStatus := .incomplete
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

/-- Compute a content hash for a declaration.
For theorems, hashes only the type (proof-irrelevant).
For data-carrying declarations, hashes type + value/fields/constructors. -/
def computeHash (env : Environment) (name : Name) (ci : ConstantInfo) : UInt64 := Id.run do
  let mut h := ci.type.hash
  match ci with
  | .thmInfo _    => ()
  | .defnInfo di  => h := mixHash h di.value.hash
  | .opaqueInfo oi => h := mixHash h oi.value.hash
  | .axiomInfo _  => ()
  | .ctorInfo _   => ()
  | .recInfo _    => ()
  | .quotInfo _   => ()
  | .inductInfo _ => ()
  if let some sinfo := getStructureInfo? env name then
    for field in sinfo.fieldNames do
      if let some projInfo := env.find? (name ++ field) then
        h := mixHash h projInfo.type.hash
  if let .inductInfo ii := ci then
    for ctorName in ii.ctors do
      if let some ctorInfo := env.find? ctorName then
        h := mixHash h ctorInfo.type.hash
  return h

/-- Compute the transitive closure of data-carrying dependencies for a declaration
and return their hashes. Uses `collectDeps` for the raw transitive closure,
then resolves derivatives to user-facing parents and hashes each.
Theorem proofs are skipped but their types are followed. -/
def computeDepHashes (env : Environment) (name : Name) (ci : ConstantInfo)
    : Array (Name × UInt64) := Id.run do
  let rawDeps := collectDeps env name ci
  -- Resolve derivatives to user-facing parents, deduplicate
  let mut resolved : NameSet := {}
  for dep in rawDeps.toArray do
    resolved := resolved.insert (resolveToUser env dep)
  -- Hash all resolved deps
  let mut result : Array (Name × UInt64) := #[]
  for dep in resolved.toArray.qsort Name.lt do
    let some depCi := env.find? dep | continue
    result := result.push (dep, computeHash env dep depCi)
  return result

/-- The `@[informal]` attribute syntax. -/
declare_syntax_cat informalStatus
syntax "complete" : informalStatus
syntax "incomplete" : informalStatus

syntax (name := informal) "informal" str (ppSpace str)? (ppSpace informalStatus)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `informal
  descr := "Tag a declaration with a paper reference and record a content snapshot."
  add := fun decl stx _attrKind => do
    let (paperRef, comment, status) ← match stx with
      | `(attr| informal $ref $[$cmt]? $[$st:informalStatus]?) => do
        let s : DeclStatus ← match st with
          | some stx => match stx with
            | `(informalStatus| complete) => pure .complete
            | _ => pure .incomplete
          | none => pure .incomplete
        pure (ref.getString, (cmt.map (·.getString)).getD "", s)
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
      status
      contentHash
      depHashes
    })
  applicationTime := .afterCompilation
}

end Informal

end
