/-
Test: signature and paperStatus fields in extractor output.
-/
import Test.Signature.Defs

open Lean Elab Command Meta Informal

/--
info: bar: sig="1 = 1" status="incomplete" ref="Theorem 2.1"
foo: sig="Nat → Nat" status="complete" ref="Definition 1.1"
untagged: sig="Bool" status=none ref=none
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let entries ← liftCoreM <| collectDecls `Test.Signature.Defs
  for i in [:entries.size] do
    let e := entries[i]!
    let name := e.declName.splitOn "." |>.getLast!
    let sig := e.signature.getD "?"
    let status := match e.paperStatus with | some s => s!"\"{s}\"" | none => "none"
    let ref := match e.paperRef with | some r => s!"\"{r}\"" | none => "none"
    IO.println s!"{name}: sig=\"{sig}\" status={status} ref={ref}"
