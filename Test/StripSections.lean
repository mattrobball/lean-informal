/-
Test: verify empty section stripping for named and anonymous sections,
including noncomputableSection entries.
-/
import Informal

open Lean Informal.EmitStandalone

-- Test 1: named section with only variable inside
#eval do
  IO.println "── Test 1: named section ──"
  let entries : Array CommandEntry := #[
    { cls := .context, src := "namespace Foo", kind := ``Parser.Command.namespace },
    { cls := .context, src := "section Bar", kind := ``Parser.Command.«section» },
    { cls := .context, src := "variable (x : Nat)", kind := ``Parser.Command.variable },
    { cls := .context, src := "end Bar", kind := ``Parser.Command.«end» },
    { cls := .tfbDecl false, src := "def baz := 42", kind := ``Parser.Command.declaration },
    { cls := .context, src := "end Foo", kind := ``Parser.Command.«end» }
  ]
  let stripped := stripEmptySections entries
  IO.println s!"  {entries.size} → {stripped.size}"
  for e in stripped do IO.println s!"  {e.kind} | {e.src}"

-- Test 2: noncomputableSection (should NOT be stripped if it has TFB decls inside)
#eval do
  IO.println "── Test 2: noncomputable section with TFB ──"
  let entries : Array CommandEntry := #[
    { cls := .context, src := "noncomputable section", kind := ``Parser.Command.«section» },
    { cls := .context, src := "open Foo", kind := ``Parser.Command.open },
    { cls := .tfbDecl false, src := "def x := 1", kind := ``Parser.Command.declaration },
    { cls := .context, src := "end", kind := ``Parser.Command.«end» }
  ]
  let stripped := stripEmptySections entries
  IO.println s!"  {entries.size} → {stripped.size} (should be 4)"

-- Test 3: what the actual QuasiAbelian module would look like
#eval do
  IO.println "── Test 3: realistic QuasiAbelian pattern ──"
  let entries : Array CommandEntry := #[
    { cls := .context, src := "open CategoryTheory", kind := ``Parser.Command.open },
    { cls := .context, src := "namespace CategoryTheory", kind := ``Parser.Command.namespace },
    { cls := .context, src := "section Strict", kind := ``Parser.Command.«section» },
    { cls := .context, src := "variable {X Y : C}", kind := ``Parser.Command.variable },
    { cls := .tfbDecl false, src := "def IsStrict ...", kind := ``Parser.Command.declaration },
    { cls := .context, src := "end Strict", kind := ``Parser.Command.«end» },
    { cls := .context, src := "section StrictSubobjectTransfer", kind := ``Parser.Command.«section» },
    { cls := .context, src := "variable {A : Type u} ...", kind := ``Parser.Command.variable },
    { cls := .context, src := "end StrictSubobjectTransfer", kind := ``Parser.Command.«end» },
    { cls := .context, src := "end CategoryTheory", kind := ``Parser.Command.«end» }
  ]
  let stripped := stripEmptySections entries
  IO.println s!"  {entries.size} → {stripped.size} (should be 7, StrictSubobjectTransfer removed)"
  for e in stripped do IO.println s!"  {e.src}"

-- Test 4: what if section kind is wrong? Check actual kinds
#eval do
  IO.println "── Test 4: Syntax kind check ──"
  IO.println s!"  «section» = {``Parser.Command.«section»}"
  IO.println s!"  «end» = {``Parser.Command.«end»}"
  IO.println s!"  noncomputableSection exists? checking..."
  -- Check if noncomputableSection is a separate kind
  IO.println s!"  declaration = {``Parser.Command.declaration}"
