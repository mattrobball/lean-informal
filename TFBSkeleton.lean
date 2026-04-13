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

open Lean Informal.EmitStandalone Informal.Cli

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [root, target, output] =>
    let rootName := root.toName
    let targetName := target.toName
    let env ← loadProjectEnv rootName
    emitStandalone env rootName targetName output
  | _ =>
    IO.eprintln "Usage: lake exe tfb_skeleton <rootPrefix> <targetDecl> <outputPath>"
    IO.Process.exit 1
