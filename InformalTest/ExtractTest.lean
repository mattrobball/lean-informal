/-
Test: simulate TFB extraction on a small sample.
Verify that only TFB declarations are emitted and sorry injection works.
-/
import Lean

open Lean Elab Command Meta

private def sampleFile := "
import Lean

universe u

namespace Foo

structure Bar (α : Type u) where
  x : α
  y : Nat

def Bar.sum (b : Bar Nat) : Nat := b.x + b.y

theorem Bar.sum_comm (b : Bar Nat) : b.x + b.y = b.y + b.x := by omega

def helper : Nat := 17

theorem uses_helper : helper = 17 := rfl

abbrev MyAlias := Bar Nat

end Foo
"

-- Simulate: TFB = {Foo.Bar, Foo.Bar.sum, Foo.Bar.sum_comm, Foo.MyAlias}
-- NOT in TFB: Foo.helper, Foo.uses_helper

def findDeclVal? (root : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.declValSimple ||
       k == ``Parser.Command.declValEqns ||
       k == ``Parser.Command.whereStructInst then
      match stx.getPos?, stx.getTailPos? with
      | some s, some e => return some (s, e)
      | _, _ => pure ()
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return none

def hasSorryableKind (root : Syntax) : Bool := Id.run do
  let mut worklist : Array Syntax := #[root]
  while !worklist.isEmpty do
    let stx := worklist.back!
    worklist := worklist.pop
    let k := stx.getKind
    if k == ``Parser.Command.theorem ||
       k == ``Parser.Command.definition ||
       k == ``Parser.Command.instance then
      return true
    for arg in stx.getArgs do
      worklist := worklist.push arg
  return false

def isContextCmd (stx : Syntax) : Bool :=
  let k := stx.getKind
  k == ``Parser.Command.namespace ||
  k == ``Parser.Command.«end» ||
  k == ``Parser.Command.open ||
  k == ``Parser.Command.variable ||
  k == ``Parser.Command.«section» ||
  k == ``Parser.Command.set_option ||
  k == ``Parser.Command.universe

#eval show MetaM Unit from do
  let inputCtx := Parser.mkInputContext sampleFile "<test>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (fileEnv, messages) ← Elab.processHeader header {} messages inputCtx (trustLevel := 1024)
  let cmdState := { Command.mkState fileEnv messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let trees := finalState.commandState.infoState.trees.toArray

  -- Simulate TFB names with their byte positions
  -- We need to find the byte positions of the TFB declarations.
  -- In a real scenario these come from DeclarationRanges + FileMap.
  -- Here we'll use the env to find which commands declare which names.
  let mut tfbNames : Std.HashSet Name := {}
  tfbNames := tfbNames.insert `Foo.Bar
  tfbNames := tfbNames.insert `Foo.Bar.sum
  tfbNames := tfbNames.insert `Foo.Bar.sum_comm
  tfbNames := tfbNames.insert `Foo.MyAlias

  -- Build tfbRangeMap: for each TFB name, find its DeclarationRanges
  let env := finalState.commandState.env
  let fileMap := FileMap.ofString sampleFile
  let mut tfbRangeMap : Std.HashMap String.Pos.Raw Name := {}
  for name in tfbNames do
    if let some ranges := declRangeExt.find? (level := .exported) env name then
      let bytePos := fileMap.ofPosition ranges.range.pos
      tfbRangeMap := tfbRangeMap.insert bytePos name
      IO.println s!"TFB: {name} at byte {bytePos} (line {ranges.range.pos.line})"

  IO.println ""
  IO.println "═══ Extraction ═══"
  IO.println ""

  let mut output := ""
  for i in [:trees.size] do
    let tree := trees[i]!
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

    -- Skip header
    if stx.getKind == ``Parser.Module.header then continue

    -- Match to TFB by position
    let mut declaredTFBName : Option Name := none
    for (pos, name) in tfbRangeMap do
      if pos >= cmdStart && pos < cmdEnd then
        declaredTFBName := some name
        break

    match declaredTFBName with
    | some name =>
      if hasSorryableKind stx then
        if let some (valStart, _) := findDeclVal? stx then
          let beforeVal := (Substring.Raw.mk sampleFile cmdStart valStart).toString
          output := output ++ beforeVal ++ " := sorry\n"
          IO.println s!"SORRY: {name}"
        else
          output := output ++ cmdSrc ++ "\n"
          IO.println s!"KEEP (no declVal): {name}"
      else
        output := output ++ cmdSrc ++ "\n"
        IO.println s!"KEEP (structure/class): {name}"
    | none =>
      if isContextCmd stx then
        output := output ++ cmdSrc ++ "\n"
        IO.println s!"CONTEXT: {stx.getKind}"
      else
        IO.println s!"SKIP: {stx.getKind} [{cmdStart}..{cmdEnd}]"

  -- Prepend import and write to file
  let fullOutput := "import Lean\n\n" ++ output
  IO.println ""
  IO.println "═══ Output ═══"
  IO.println fullOutput

  -- Write to temp file for manual compilation test
  IO.FS.writeFile "/tmp/tfb_test_output.lean" fullOutput
  IO.println "Wrote /tmp/tfb_test_output.lean"
