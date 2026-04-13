/-
lake exe extract_decls — extract all user-facing declarations from a compiled
project to a JSON file.

Usage (from the downstream project directory):
  lake exe extract_decls <rootPrefix> <outputPath>

Example:
  lake exe extract_decls BridgelandStability extracted.json
-/
import Informal

open Lean Informal.Cli

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [root, output] =>
    let rootName := root.toName
    let env ← loadProjectEnv rootName
    let entries ← runCoreM env (collectDecls rootName)
    IO.FS.writeFile output (Lean.toJson entries).pretty
    IO.println s!"Extracted {entries.size} declarations to {output}"
  | _ =>
    IO.eprintln "Usage: lake exe extract_decls <rootPrefix> <outputPath>"
    IO.Process.exit 1
