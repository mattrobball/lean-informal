/-
Copyright (c) 2026 Matthew Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Ballard
-/
module

public meta import Informal.Attr
public meta import Verso.Code.External
public meta import SubVerso.Module

/-!
# Informal Verso block expanders

Two Verso code-block expanders for rendering `@[informal]`-tagged declarations
inside a Verso manual.

* ``` ```informalDecl (name := Foo.Bar) ``` ``` — renders a single declaration by
  its fully-qualified name. The declaration's full command source is looked up
  in Verso's per-module `ModuleItem` cache (populated by SubVerso's
  `subverso-extract-mod`), matched by `defines : Array Name`, and emitted via
  Verso's `leanBlock`. Works for any declaration kind; the full body appears
  for `def`/`abbrev`/`class`/`structure`/`instance`/`inductive`. `theorem`
  bodies are included inline — wrap in `{collapsibleProof}` at the call site if
  you want a collapsed proof.

* ``` ```informalByRef (paperRef := "Theorem 1.2") ``` ``` — convenience:
  looks up every `@[informal "Theorem 1.2"]`-tagged entry via
  `Informal.getEntriesFor` and emits one `leanBlock` per match. Emits a
  "Not yet formalized in this project." placeholder block when zero matches.

Both expanders require the ambient Verso genre to have a `Verso.Code.External.ExternalCode`
instance (the manual genre does).
-/

public meta section

open Lean Elab
open Verso Doc Elab Log ArgParse
open SubVerso Highlighting
open SubVerso.Module (ModuleItem)
open Verso.Code.External
open Verso.Code.External.ExternalCode

namespace Informal.VersoBlock

/-- Resolve a declaration name to the module it is defined in, via the
environment's module index. Returns `none` if the declaration is not imported. -/
def moduleOfDecl? (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  return env.header.moduleNames[idx.toNat]!

/-- Configuration for `{informalDecl}`. `name` is the fully-qualified
declaration to render; `project` is the directory containing the declaration's
source (defaults to `verso.exampleProject` when unspecified). -/
structure InformalDeclContext where
  /-- The declaration to render. -/
  name : Ident
  /-- Project directory containing the declaration's source. -/
  project : StrLit

@[no_expose]
public instance [Monad m] [MonadOptions m] [MonadError m] [MonadLiftT CoreM m] :
    FromArgs InformalDeclContext m where
  fromArgs :=
    (fun name project => ({ name, project } : InformalDeclContext)) <$>
      .named `name .ident false <*>
      projectOrDefault

/-- Render a single `@[informal]`-tagged declaration by name.

```
```informalDecl (name := CategoryTheory.Triangulated.Foo)
```
```
-/
@[code_block_expander informalDecl]
public meta def informalDecl : CodeBlockExpander
  | args, _code => withTraceNode `Elab.Verso (fun _ => pure m!"informalDecl") <| do
    let cfg ← parseThe InformalDeclContext args
    let env ← getEnv
    let name := cfg.name.getId
    let some modName := moduleOfDecl? env name
      | throwErrorAt cfg.name m!"Declaration '{name}' is not in the current environment; \
          ensure its module is imported by the Verso manual."
    let items ← loadModuleContent cfg.project modName.toString
    let some item := items.find? (·.defines.contains name)
      | throwErrorAt cfg.name m!"Declaration '{name}' was not found in the module-item cache \
          for '{modName}'. (If the declaration is macro-generated or produced by an elaborator, \
          no matching command source may exist.)"
    let codeCfg : CodeConfig := {}
    pure #[← ``(Verso.Code.External.ExternalCode.leanBlock
                  $(quote item.code) $(quote codeCfg))]

/-- Configuration for `{informalByRef}`. -/
structure InformalByRefContext where
  /-- The paper reference to join against `@[informal "..."]` tags. -/
  paperRef : StrLit
  /-- Project directory containing the declaration sources. -/
  project : StrLit

@[no_expose]
public instance [Monad m] [MonadOptions m] [MonadError m] [MonadLiftT CoreM m] :
    FromArgs InformalByRefContext m where
  fromArgs :=
    (fun paperRef project => ({ paperRef, project } : InformalByRefContext)) <$>
      .named `paperRef .strLit false <*>
      projectOrDefault

/-- Render every `@[informal "paperRef"]`-tagged declaration that matches, one
`leanBlock` per match. Emits a "Not yet formalized in this project." paragraph
when there are no matches.

```
```informalByRef (paperRef := "Theorem 1.2")
```
```
-/
@[code_block_expander informalByRef]
public meta def informalByRef : CodeBlockExpander
  | args, _code => withTraceNode `Elab.Verso (fun _ => pure m!"informalByRef") <| do
    let cfg ← parseThe InformalByRefContext args
    let env ← getEnv
    let entries := Informal.getEntriesFor env cfg.paperRef.getString
    if entries.isEmpty then
      return #[← ``(Verso.Doc.Block.para
        #[Verso.Doc.Inline.emph #[Verso.Doc.Inline.text "Not yet formalized in this project."]])]
    let codeCfg : CodeConfig := {}
    let mut blocks : Array Term := #[]
    for entry in entries do
      let some modName := moduleOfDecl? env entry.declName | continue
      let items ← loadModuleContent cfg.project modName.toString
      if let some item := items.find? (·.defines.contains entry.declName) then
        blocks := blocks.push (← ``(Verso.Code.External.ExternalCode.leanBlock
                                      $(quote item.code) $(quote codeCfg)))
    if blocks.isEmpty then
      return #[← ``(Verso.Doc.Block.para
        #[Verso.Doc.Inline.emph #[Verso.Doc.Inline.text
          "Declarations tagged for this reference are not available in the module cache."]])]
    pure blocks

end Informal.VersoBlock

end
