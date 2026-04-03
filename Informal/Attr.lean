/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
import Lean

/-!
# Informal paper reference attribute

The `@[informal]` attribute tags a formal Lean declaration with a reference
to a statement in a mathematical paper or text. It stores the reference in a
persistent environment extension, making it available for documentation
generation, drift detection, and cross-referencing tooling.

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

open Lean Elab

namespace Informal

/-- An informal paper reference entry stored in the environment. -/
structure Entry where
  /-- The Lean declaration name. -/
  declName : Name
  /-- The paper reference, e.g., "Definition 5.1", "Theorem 7.1". -/
  paperRef : String
  /-- Optional comment or gloss. -/
  comment : String := ""
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

/-- The `@[informal]` attribute syntax. -/
syntax (name := informal) "informal" str (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `informal
  descr := "Tag a declaration with a paper reference."
  add := fun decl stx _attrKind => do
    let (paperRef, comment) ← match stx with
      | `(attr| informal $ref $[$cmt]?) =>
        pure (ref.getString, (cmt.map (·.getString)).getD "")
      | _ => throwUnsupportedSyntax
    modifyEnv (informalExt.addEntry · { declName := decl, paperRef, comment })
  applicationTime := .afterTypeChecking
}

end Informal
