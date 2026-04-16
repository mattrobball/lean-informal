/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Informal.Attr

/-!
# Export, query, and check commands for informal paper references
-/

public meta section

open Lean Elab Command Meta Informal

/-- JSON-serializable informal entry with module name resolved. -/
structure InformalExportEntry where
  declName : String
  moduleName : String
  paperRef : String
  comment : String
  status : String
  contentHash : Nat
  depHashes : Array (String × Nat)
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
      comment := e.comment
      status := toString e.status
      contentHash := e.contentHash.toNat
      depHashes := e.depHashes.map fun (n, h) => (n.toString, h.toNat) }

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

/-- `#check_informal` — verify that all `@[informal]` entries are still consistent
with the current state of their declarations and dependencies.

Reports warnings for:
- Declarations whose content hash has changed
- Dependencies whose content hash has changed
- Declarations or dependencies that no longer exist -/
elab "#check_informal" : command => do
  let env ← getEnv
  let entries := getEntries env
  if entries.isEmpty then
    logInfo "No informal entries to check."
    return
  let mut issues := 0
  for entry in entries do
    let some ci := env.find? entry.declName | do
      logWarning m!"@[informal \"{entry.paperRef}\"] on {.ofConstName entry.declName}: \
        declaration no longer exists"
      issues := issues + 1
      continue
    let currentHash := computeHash env entry.declName ci
    if currentHash != entry.contentHash then
      logWarning m!"@[informal \"{entry.paperRef}\"] on {.ofConstName entry.declName}: \
        declaration changed (hash {entry.contentHash.toNat} → {currentHash.toNat})"
      issues := issues + 1
    for (depName, storedHash) in entry.depHashes do
      let some depCi := env.find? depName | do
        logWarning m!"@[informal \"{entry.paperRef}\"] on {.ofConstName entry.declName}: \
          dependency {.ofConstName depName} no longer exists"
        issues := issues + 1
        continue
      let currentDepHash := computeHash env depName depCi
      if currentDepHash != storedHash then
        logWarning m!"@[informal \"{entry.paperRef}\"] on {.ofConstName entry.declName}: \
          dependency {.ofConstName depName} changed \
          (hash {storedHash.toNat} → {currentDepHash.toNat})"
        issues := issues + 1
  if issues == 0 then
    logInfo m!"All {entries.size} informal entries are consistent."
  else
    logWarning m!"{issues} issue(s) found across {entries.size} informal entries."

end
