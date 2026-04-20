/-
Copyright (c) 2025 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Informal.Attr
public meta import Informal.Classify
public meta import Lean.DocString

/-!
# Declaration extraction

Walks a compiled Lean environment and emits a JSON array of all user-facing
declarations with metadata, `@[informal]` paper references, docstrings,
source ranges, and content hashes for staleness detection.

## Usage

In a project that depends on `informal`, add to any Lean file:

```
import MyProject
import Informal

#extract_decls `MyProject "extracted.json"
```

This writes `extracted.json` at elaboration time.
-/

public meta section

open Lean Elab Command Meta Informal

/-- Classification of declaration kinds. -/
inductive DeclKind where
  | «theorem» | «def» | «structure» | «class» | «abbrev»
  | «instance» | «inductive» | «axiom» | «opaque»
  deriving BEq, Repr

instance : ToString DeclKind where
  toString
    | .theorem => "theorem"
    | .def => "def"
    | .structure => "structure"
    | .class => "class"
    | .abbrev => "abbrev"
    | .instance => "instance"
    | .inductive => "inductive"
    | .axiom => "axiom"
    | .opaque => "opaque"

/-- JSON output entry for a declaration. -/
structure DeclEntry where
  declName : String
  declKind : String
  moduleName : String
  docstring : Option String := none
  signature : Option String := none
  contentHash : UInt64 := 0
  depHashes : Array (String × UInt64) := #[]
  paperRef : Option String := none
  paperComment : Option String := none
  paperStatus : Option String := none
  sourceFile : Option String := none
  startLine : Option Nat := none
  endLine : Option Nat := none
  deriving Inhabited

instance : ToJson DeclEntry where
  toJson e := Json.mkObj [
    ("declName", Json.str e.declName),
    ("declKind", Json.str e.declKind),
    ("moduleName", Json.str e.moduleName),
    ("docstring", match e.docstring with | some d => Json.str d | none => Json.null),
    ("signature", match e.signature with | some s => Json.str s | none => Json.null),
    ("contentHash", Json.num (Lean.JsonNumber.fromNat e.contentHash.toNat)),
    ("depHashes", if e.depHashes.isEmpty then Json.null
      else Json.arr (e.depHashes.map fun (n, h) =>
        Json.mkObj [("name", Json.str n), ("hash", Json.num (.fromNat h.toNat))])),
    ("paperRef", match e.paperRef with | some r => Json.str r | none => Json.null),
    ("paperComment", match e.paperComment with | some c => Json.str c | none => Json.null),
    ("paperStatus", match e.paperStatus with | some s => Json.str s | none => Json.null),
    ("sourceFile", match e.sourceFile with | some s => Json.str s | none => Json.null),
    ("startLine", match e.startLine with | some n => Json.num (.fromNat n) | none => Json.null),
    ("endLine", match e.endLine with | some n => Json.num (.fromNat n) | none => Json.null)
  ]

/-- Classify a constant into a `DeclKind`. Uses `CoreM` for instance/reducibility checks. -/
def classifyDecl (env : Environment) (name : Name) (ci : ConstantInfo) : CoreM DeclKind := do
  match ci with
  | .thmInfo _ =>
    if (← isInstance name) then return .instance else return .theorem
  | .inductInfo _ =>
    if isStructure env name then
      if isClass env name then return .class else return .structure
    else return .inductive
  | .defnInfo _ =>
    if isStructure env name then
      if isClass env name then return .class else return .structure
    else if (← isInstance name) then return .instance
    else if (← isReducible name) then return .abbrev
    else return .def
  | .axiomInfo _ => return .axiom
  | .opaqueInfo _ => return .opaque
  | .ctorInfo _ => return .def
  | .recInfo _ => return .def
  | .quotInfo _ => return .def

/-- Resolve the module name for a declaration. -/
def getModuleName (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString
  | none => "unknown"

/-- Walk the environment and collect all user-facing declarations under `rootPrefix`.
    Includes `@[informal]` data, docstrings, source ranges, and content hashes.

    Also emits a second pass for `#informal_external` entries whose target
    decls live outside `rootPrefix` (e.g. mathlib).  These are included so
    downstream tools (the comparison dashboard) can surface upstream-
    formalized paper references without a local host decl. -/
def collectDecls (rootPrefix : Name) : CoreM (Array DeclEntry) := do
  let env ← getEnv
  let informalEntries := Informal.getEntries env
  let informalMap : Std.HashMap Name Informal.Entry :=
    informalEntries.foldl (init := {}) fun m e => m.insert e.declName e
  let mut result : Array DeclEntry := #[]
  let mut emitted : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[i]!
    unless rootPrefix.isPrefixOf modName do continue
    let modData := env.header.moduleData[i]!
    for j in [:modData.constNames.size] do
      let name := modData.constNames[j]!
      let some ci := env.find? name | continue
      if (classifyNonUser env name).isSome then continue
      -- Additional filter: no declaration ranges means compiler-generated.
      -- This runs in CoreM where findDeclarationRanges? is reliable
      -- (unlike during afterCompilation where declRangeExt may not be populated).
      unless (← findDeclarationRanges? name).isSome do continue
      let kind ← classifyDecl env name ci
      let hash := computeHash env name ci
      let doc ← (Lean.findDocString? env name : IO _)
      let informal? := informalMap[name]?
      let range? ← findDeclarationRanges? name
      let sourceFile := modName.toString.replace "." "/" ++ ".lean"
      let sig ← MetaM.run' (ppExpr ci.type)
      let entry : DeclEntry := {
        declName := name.toString
        declKind := toString kind
        moduleName := getModuleName env name
        docstring := doc
        signature := some (toString sig)
        contentHash := hash
        depHashes := match informal? with
          | some e => e.depHashes.map fun (n, h) => (n.toString, h)
          | none => #[]
        paperRef := informal?.map (·.paperRef)
        paperComment := informal?.bind fun e =>
          if e.comment.isEmpty then none else some e.comment
        paperStatus := informal?.map fun e => toString e.status
        sourceFile := some sourceFile
        startLine := range?.map (·.range.pos.line + 1)
        endLine := range?.map (·.range.endPos.line + 1)
      }
      result := result.push entry
      emitted := emitted.insert name
  -- Second pass: `#informal_external` entries pointing at decls outside
  -- `rootPrefix`.  These have no local host, so the first pass skipped
  -- them.  Emit a DeclEntry using the external decl's env metadata
  -- (moduleName, source file, signature).  Downstream renderers can
  -- distinguish externals by checking whether the moduleName starts with
  -- the root prefix.
  for ie in informalEntries do
    if emitted.contains ie.declName then continue
    let some ci := env.find? ie.declName | continue
    let kind ← classifyDecl env ie.declName ci
    let hash := computeHash env ie.declName ci
    let doc ← (Lean.findDocString? env ie.declName : IO _)
    let range? ← findDeclarationRanges? ie.declName
    let modName := getModuleName env ie.declName
    let sourceFile := modName.replace "." "/" ++ ".lean"
    let sig ← MetaM.run' (ppExpr ci.type)
    result := result.push {
      declName := ie.declName.toString
      declKind := toString kind
      moduleName := modName
      docstring := doc
      signature := some (toString sig)
      contentHash := hash
      depHashes := ie.depHashes.map fun (n, h) => (n.toString, h)
      paperRef := some ie.paperRef
      paperComment := if ie.comment.isEmpty then none else some ie.comment
      paperStatus := some (toString ie.status)
      sourceFile := some sourceFile
      startLine := range?.map (·.range.pos.line + 1)
      endLine := range?.map (·.range.endPos.line + 1)
    }
  return result.qsort fun a b =>
    if a.moduleName == b.moduleName then a.declName < b.declName
    else a.moduleName < b.moduleName

/-- `#extract_decls rootPrefix "path.json"` — extract all declarations under `rootPrefix`
    to a JSON file. Runs at elaboration time. -/
elab "#extract_decls" root:ident path:str : command => do
  let rootPrefix := root.getId
  let entries ← liftCoreM <| collectDecls rootPrefix
  let json := Lean.toJson entries
  IO.FS.writeFile path.getString json.pretty
  logInfo m!"Extracted {entries.size} declarations to {path.getString}"

end
