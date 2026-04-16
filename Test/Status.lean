/-
Test: @[informal] attribute status syntax and storage.
-/
import Informal

open Lean Informal

namespace Test.Status

@[informal "Definition 1.1"]
def noStatus : Nat := 42

@[informal "Theorem 2.1" "only forward direction"]
theorem commentNoStatus : True := trivial

@[informal "Lemma 3.1" complete]
theorem explicitComplete : 1 = 1 := rfl

@[informal "Proposition 4.1" "generalized" complete]
def commentAndComplete : Nat := 0

@[informal "Theorem 5.1" incomplete]
theorem explicitIncomplete : 2 = 2 := rfl

@[informal "Lemma 6.1" "partial coverage" incomplete]
theorem commentAndIncomplete : 3 = 3 := rfl

end Test.Status

/--
info: Test.Status.noStatus: ref="Definition 1.1" comment="" status=incomplete
Test.Status.commentNoStatus: ref="Theorem 2.1" comment="only forward direction" status=incomplete
Test.Status.explicitComplete: ref="Lemma 3.1" comment="" status=complete
Test.Status.commentAndComplete: ref="Proposition 4.1" comment="generalized" status=complete
Test.Status.explicitIncomplete: ref="Theorem 5.1" comment="" status=incomplete
Test.Status.commentAndIncomplete: ref="Lemma 6.1" comment="partial coverage" status=incomplete
-/
#guard_msgs in
#eval show MetaM Unit from do
  let entries := getEntries (← getEnv)
  for i in [:entries.size] do
    let e := entries[i]!
    IO.println s!"{e.declName}: ref=\"{e.paperRef}\" comment=\"{e.comment}\" status={e.status}"
