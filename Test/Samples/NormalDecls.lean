/-
Sample: normal declarations (no macros, no custom elaborators).
Target: `NormalDecls.main_theorem`
Expected TFB: MyStruct, MyStruct.value, helper, main_theorem
-/

structure MyStruct (α : Type) where
  data : α
  count : Nat

def MyStruct.value (s : MyStruct Nat) : Nat := s.data + s.count

def helper : Nat := 42

theorem main_theorem (s : MyStruct Nat) : s.data + s.count ≥ s.count := Nat.le_add_left _ _
