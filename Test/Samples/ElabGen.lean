/-
Sample: custom elaborator that generates declarations.
Target: `ElabGen.myMagicNumber_is_42`
Expected: rangeless decl pretty-printed from env with actual value.
-/
import Lean

open Lean Elab Command Term

syntax "make_const " ident " := " num : command

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

make_const myMagicNumber := 42

theorem myMagicNumber_is_42 : myMagicNumber = 42 := rfl
