/-
Test: a custom command elaborator that generates declarations.
Unlike a macro (which returns Syntax), an elaborator directly adds
to the environment via addAndCompile.
-/
import Lean

open Lean Elab Command Term

-- Define syntax
syntax "make_const " ident " := " num : command

-- Elaborate: directly add a Nat constant to the environment
elab_rules : command
  | `(command| make_const $name := $val) => do
    let declName := name.getId
    let n := val.getNat
    liftTermElabM do
      addAndCompile <| .defnDecl {
        name := declName
        levelParams := []
        type := mkConst ``Nat
        value := mkNatLit n
        hints := .regular 0
        safety := .safe
      }

-- Use the elaborator
make_const myMagicNumber := 42

-- A theorem about the elaborator-generated constant
theorem myMagicNumber_is_42 : myMagicNumber = 42 := rfl
