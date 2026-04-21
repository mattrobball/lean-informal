/-
Test: a single declaration may carry multiple `@[informal]` attributes,
one per paper statement it realizes. Each tag adds its own environment
entry; `getEntries` / `getEntriesFor` must surface all of them.
-/
import Informal

open Lean Informal

namespace Test.MultiTag

@[informal "Definition 1.1" complete,
  informal "Definition 5.1" complete]
structure DualTag where
  x : Nat

@[informal "Theorem 7.1" "class-map-general form",
  informal "Corollary 7.2" "the identity-class-map specialization" complete]
theorem dualTheorem : 1 = 1 := rfl

end Test.MultiTag

/--
info: Test.MultiTag.DualTag: ref="Definition 1.1" status=complete
Test.MultiTag.DualTag: ref="Definition 5.1" status=complete
Test.MultiTag.dualTheorem: ref="Theorem 7.1" status=incomplete
Test.MultiTag.dualTheorem: ref="Corollary 7.2" status=complete
-/
#guard_msgs in
#eval show MetaM Unit from do
  let entries := (getEntries (← getEnv)).filter fun e =>
    e.declName == ``Test.MultiTag.DualTag ∨ e.declName == ``Test.MultiTag.dualTheorem
  for e in entries do
    IO.println s!"{e.declName}: ref=\"{e.paperRef}\" status={e.status}"

-- `getEntriesFor` must pick out only the matching tag.
/--
info: found 1 entry for Definition 1.1:
  Test.MultiTag.DualTag
-/
#guard_msgs in
#eval show MetaM Unit from do
  let env ← getEnv
  let es := (getEntriesFor env "Definition 1.1").filter (·.declName == ``Test.MultiTag.DualTag)
  IO.println s!"found {es.size} entry for Definition 1.1:"
  for e in es do
    IO.println s!"  {e.declName}"
