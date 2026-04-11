/-
lake exe tfb_skeleton — generate a standalone TFB file from a compiled project.

Usage (from the downstream project directory):
  lake exe tfb_skeleton <rootPrefix> <targetDecl> <outputPath>

Example:
  lake exe tfb_skeleton BridgelandStability \
    CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent \
    artifacts/trusted_base.lean
-/
import Informal

open Lean Informal.EmitStandalone

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [root, target, output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let rootName := root.toName
    let targetName := target.toName
    -- Import the project module
    let env ← importModules (loadExts := true) #[{ module := rootName }] {} (trustLevel := 1024)
    emitStandalone env rootName targetName output
  | _ =>
    IO.eprintln "Usage: lake exe tfb_skeleton <rootPrefix> <targetDecl> <outputPath>"
    IO.Process.exit 1
