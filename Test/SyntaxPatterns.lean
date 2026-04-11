/-
Test file: investigate Syntax patterns for different declaration kinds.
Goal: understand how to extract individual declarations from InfoTrees
and how to find/replace declVal nodes for sorry injection.
-/
import Lean

open Lean Elab Command Meta

-- ══ Sample declarations to parse ══

private def sampleFile := "
import Lean

universe u v

open Lean

namespace Foo

structure Bar (α : Type u) where
  x : α
  y : Nat

def Bar.sum (b : Bar Nat) : Nat := b.x + b.y

theorem Bar.sum_pos (b : Bar Nat) (h : 0 < b.x) : 0 < b.sum := by omega

abbrev MyType := Nat

noncomputable def myDef : Nat := 42

instance : ToString (Bar Nat) where
  toString b := toString b.x ++ toString b.y

class Pointed (α : Type u) where
  point : α

lemma trivial_lemma : True := trivial

end Foo
"

-- ══ Syntax investigation ══

/-- Find declVal nodes in a Syntax tree. -/
def findDeclVals (root : Syntax) : Array (SyntaxNodeKind × String.Pos.Raw × String.Pos.Raw) := Id.run do
  let mut worklist : Array Syntax := #[root]
  let mut results : Array (SyntaxNodeKind × String.Pos.Raw × String.Pos.Raw) := #[]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.declValSimple ||
       k == ``Parser.Command.declValEqns ||
       k == ``Parser.Command.whereStructInst then
      match stx.getPos?, stx.getTailPos? with
      | some s, some e => results := results.push (k, s, e)
      | _, _ => pure ()
    for arg in stx.getArgs do
      worklist := worklist.push arg
  results

/-- Check what declaration kind a Syntax node represents. -/
def findDeclKind (root : Syntax) : Option SyntaxNodeKind := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.theorem ||
       k == ``Parser.Command.definition ||
       k == ``Parser.Command.instance ||
       k == ``Parser.Command.structure ||
       k == ``Parser.Command.classInductive ||
       k == ``Parser.Command.«abbrev» ||
       k == ``Parser.Command.declaration then
      return some k
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return none

-- ══ Test: parse the sample file and inspect each command ══

#eval show MetaM Unit from do
  let env ← getEnv
  let inputCtx := Parser.mkInputContext sampleFile "<test>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- Use a minimal env (just Init) for elaboration
  let (fileEnv, messages) ← Elab.processHeader header {} messages inputCtx (trustLevel := 1024)
  let cmdState := { Command.mkState fileEnv messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let trees := finalState.commandState.infoState.trees.toArray
  IO.println s!"Total InfoTrees: {trees.size}"
  IO.println ""

  for i in [:trees.size] do
    let tree := trees[i]!
    -- Extract CommandInfo
    let cmdResult := tree.foldInfo (init := none) fun _ctx info acc =>
      match acc with
      | some _ => acc
      | none =>
        match info with
        | .ofCommandInfo ci => some ci.stx
        | _ => none
    let some stx := cmdResult | continue
    let some cmdStart := stx.getPos? | continue
    let some cmdEnd := stx.getTailPos? | continue
    let cmdSrc := (Substring.Raw.mk sampleFile cmdStart cmdEnd).toString
    let declVals := findDeclVals stx
    let declKind := findDeclKind stx

    IO.println s!"── Command {i} ──"
    IO.println s!"  TopKind: {stx.getKind}"
    IO.println s!"  DeclKind: {declKind}"
    IO.println s!"  Pos: [{cmdStart}..{cmdEnd}]"
    let srcPreview := if cmdSrc.length > 80 then (cmdSrc.take 80).toString ++ "..." else cmdSrc
    IO.println s!"  Source: {srcPreview}"
    IO.println s!"  declVals: {declVals.size}"
    for (kind, s, e) in declVals do
      let valSrc := (Substring.Raw.mk sampleFile s e).toString
      let valPreview := if valSrc.length > 60 then (valSrc.take 60).toString ++ "..." else valSrc
      IO.println s!"    {kind} [{s}..{e}]: {valPreview}"
    IO.println ""
