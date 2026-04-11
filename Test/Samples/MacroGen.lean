/-
Sample: macro-generated declarations.
Target: `MacroGen.MyPoint.test`
Expected: macro expands to structure, compiles clean.
-/
import Lean

open Lean Elab Command in
macro "gen_point_struct" name:ident : command =>
  `(structure $name where
      x : Nat
      y : Nat)

gen_point_struct MyPoint

def MyPoint.origin : MyPoint := ⟨0, 0⟩

@[simp] theorem MyPoint.x_origin : (MyPoint.origin).x = 0 := rfl

theorem MyPoint.test : (MyPoint.origin).x = 0 := by simp

deriving instance BEq for MyPoint

def MyPoint.eq_origin (p : MyPoint) : Bool := p == MyPoint.origin
