/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Informal.Attr

/-!
# Export and query commands for informal paper references
-/

public meta section

open Lean Elab Command Informal

/-- JSON-serializable informal entry with module name resolved. -/
structure InformalExportEntry where
  declName : String
  moduleName : String
  paperRef : String
  comment : String
  deriving ToJson, FromJson

/-- Export all informal entries, resolving module names from the environment. -/
def exportInformalEntries (env : Environment) : Array InformalExportEntry :=
  (getEntries env).map fun e =>
    let moduleName := match env.getModuleIdxFor? e.declName with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString
      | none => "unknown"
    { declName := e.declName.toString
      moduleName
      paperRef := e.paperRef
      comment := e.comment }

/-- `#informal_refs` — list all declarations tagged with `@[informal]`. -/
elab "#informal_refs" : command => do
  let entries := getEntries (← getEnv)
  if entries.isEmpty then
    logInfo "No informal entries found."
  else
    let mut msgs : Array MessageData := #[]
    for e in entries do
      let cmt := if e.comment.isEmpty then "" else s!" ({e.comment})"
      msgs := msgs.push m!"  {.ofConstName e.declName} ← {e.paperRef}{cmt}"
    logInfo <| .joinSep msgs.toList "\n"

/-- `#informal_refs_for "Theorem 7.1"` — find all declarations for a paper reference. -/
elab "#informal_refs_for" ref:str : command => do
  let entries := getEntriesFor (← getEnv) ref.getString
  if entries.isEmpty then
    logInfo m!"No declarations found for \"{ref.getString}\"."
  else
    let mut msgs : Array MessageData := #[]
    for e in entries do
      msgs := msgs.push m!"  {.ofConstName e.declName}"
    logInfo <| m!"\"{ref.getString}\":\n" ++ .joinSep msgs.toList "\n"

/-- `#export_informal "path.json"` — export all informal entries to JSON. -/
elab "#export_informal" path:str : command => do
  let entries := exportInformalEntries (← getEnv)
  let json := Lean.toJson entries
  IO.FS.writeFile path.getString json.pretty
  logInfo m!"Exported {entries.size} informal entries to {path.getString}"

end
