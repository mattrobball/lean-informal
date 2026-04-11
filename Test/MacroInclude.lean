/-
Test: includeMacroDef mode — emit the macro definition so the call works.
-/
import Informal

open Lean Informal.EmitStandalone

-- Use includeMacroDef config
#eval show MetaM Unit from do
  let env ← getEnv
  let cfg : Config := { macroHandling := .includeMacroDef }
  emitStandalone env `Test.MetaGen `MyPoint.eq_origin "/tmp/tfb_include_macro.lean"
    (cfg := cfg)
