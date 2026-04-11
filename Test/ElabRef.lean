/-
Test: elaborator-generated declaration that references other project declarations.
-/
import Lean

open Lean Elab Command Term

-- A normal structure
structure Config where
  threshold : Nat
  name : String

-- A normal def
def defaultConfig : Config := ⟨10, "default"⟩

-- Custom elaborator that generates a def referencing Config and defaultConfig
syntax "make_config_checker " ident : command

elab_rules : command
  | `(command| make_config_checker $name) => do
    let declName := name.getId
    liftTermElabM do
      let type ← elabTerm (← `(Config → Bool)) none
      let value ← elabTerm (← `(fun c => c.threshold > defaultConfig.threshold)) (some type)
      addAndCompile <| .defnDecl {
        name := declName
        levelParams := []
        type := ← instantiateMVars type
        value := ← instantiateMVars value
        hints := .regular 0
        safety := .safe
      }

make_config_checker isAboveDefault

-- A theorem about it
theorem isAboveDefault_spec (c : Config) (h : c.threshold > 10) :
    isAboveDefault c = true := by
  unfold isAboveDefault defaultConfig
  simp
  omega
