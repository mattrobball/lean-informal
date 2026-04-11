/-
End-to-end tests for tfb_skeleton.

For each sample module, generates a skeleton file and compiles it.
Asserts zero compilation errors.
-/
import Informal
import Test.Samples.NormalDecls
import Test.Samples.MacroGen
import Test.Samples.ElabGen
import Test.Samples.ElabRef

open Lean Informal.EmitStandalone

structure TestCase where
  name : String
  rootPrefix : Name
  target : Name
  deriving Inhabited

def testCases : Array TestCase := #[
  { name := "NormalDecls"
    rootPrefix := `Test.Samples.NormalDecls
    target := `main_theorem },
  { name := "MacroGen"
    rootPrefix := `Test.Samples.MacroGen
    target := `MyPoint.eq_origin },
  { name := "ElabGen"
    rootPrefix := `Test.Samples.ElabGen
    target := `myMagicNumber_is_42 },
  { name := "ElabRef"
    rootPrefix := `Test.Samples.ElabRef
    target := `isAboveDefault_spec }
]

#eval show MetaM Unit from do
  let env ← getEnv
  let mut passed := 0
  let mut failed := 0
  for tc in testCases do
    let outPath := s!"/tmp/tfb_e2e_{tc.name}.lean"
    IO.println s!"── {tc.name} ──"
    -- Generate skeleton
    try
      emitStandalone env tc.rootPrefix tc.target outPath
    catch e =>
      IO.println s!"  FAIL (generation): {← e.toMessageData.toString}"
      failed := failed + 1
      continue
    -- Compile the output by spawning lean
    let child ← IO.Process.spawn {
      cmd := "lake"
      args := #["env", "lean", outPath]
      stdout := .piped
      stderr := .piped
    }
    let stderr ← child.stderr.readToEnd
    let exitCode ← child.wait
    let hasError (s : String) : Bool := (s.splitOn "error:" |>.length) > 1
    let hasWarning (s : String) : Bool := (s.splitOn "warning:" |>.length) > 1
    let stderrLines := stderr.splitOn "\n"
    let errors := stderrLines.filter hasError |>.length
    let warnings := stderrLines.filter hasWarning |>.length
    if exitCode == 0 && errors == 0 then
      IO.println s!"  PASS ({warnings} sorry warnings)"
      passed := passed + 1
    else
      IO.println s!"  FAIL (exit={exitCode}, {errors} errors, {warnings} warnings)"
      for line in stderrLines do
        if hasError line then
          IO.println s!"    {line}"
      failed := failed + 1
  IO.println s!"\n═══ Results: {passed} passed, {failed} failed ═══"
  if failed > 0 then
    IO.eprintln s!"{failed} test(s) failed"
