/-
lake exe tfb_skeleton — generate a standalone TFB file from a compiled project.

Usage (from the downstream project directory):
  lake exe tfb_skeleton [--include-macros] <rootPrefix> <targetDecl> <outputPath>

Options:
  --include-macros  Include macro definitions instead of expanding them.
                    Default: expand macros to their output syntax.

Example:
  lake exe tfb_skeleton BridgelandStability \
    CategoryTheory.Triangulated.NumericalStabilityCondition.existsComplexManifoldOnConnectedComponent \
    artifacts/trusted_base.lean
-/
import Informal

open Lean Informal.EmitStandalone

unsafe def main (args : List String) : IO Unit := do
  let mut cfg : Config := {}
  let mut positional : Array String := #[]
  for arg in args do
    if arg == "--include-macros" then
      cfg := { cfg with macroHandling := .includeMacroDef }
    else
      positional := positional.push arg
  match positional.toList with
  | [root, target, output] =>
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let rootName := root.toName
    let targetName := target.toName
    -- Import the project module.
    -- `loadExts := true` is critical: without it, parser extensions (notation like +, ⋙,
    -- scoped syntax, etc.) are not loaded, causing `IO.processCommands` to produce
    -- truncated Syntax trees with wrong `getTailPos?` positions.
    -- Discovered via Test/ExeVsElab.lean: the elab command path gets extensions
    -- automatically from `import`, but `importModules` defaults to `loadExts := false`.
    let env ← importModules (loadExts := true) #[{ module := rootName }] {} (trustLevel := 1024)
    emitStandalone env rootName targetName output (cfg := cfg)
  | _ =>
    IO.eprintln "Usage: lake exe tfb_skeleton [--include-macros] <rootPrefix> <targetDecl> <outputPath>"
    IO.Process.exit 1
