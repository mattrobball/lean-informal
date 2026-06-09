/-
Test: compare environment state from `importModules` (exe path) vs
the elab command context (elab path). What's different?
-/
import Lean

open Lean Elab Command Meta

-- Small sample to re-elaborate
private def sampleFile := "
import Lean

universe u

namespace Foo

structure Bar (α : Type u) where
  x : α
  y : Nat

def Bar.sum (b : Bar Nat) : Nat := b.x + b.y

end Foo
"

/-- Re-elaborate sampleFile against a given env and report what we get. -/
def testReelaborate (label : String) (env : Environment) : IO Unit := do
  IO.println s!"═══ {label} ═══"
  IO.println s!"  env.header.moduleNames.size = {env.header.moduleNames.size}"
  IO.println s!"  env.contains `Lean.Name = {env.contains `Lean.Name}"

  let inputCtx := Parser.mkInputContext sampleFile "<test>"
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let cmdState := { Command.mkState env messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState

  let trees := finalState.commandState.infoState.trees.toArray
  IO.println s!"  InfoTrees: {trees.size}"

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
    let preview := if cmdSrc.length > 60 then (cmdSrc.take 60).toString ++ "..." else cmdSrc
    IO.println s!"  cmd[{i}] kind={stx.getKind} [{cmdStart}..{cmdEnd}] {preview}"

-- Test 1: elab context (what #emit_standalone uses)
#eval show MetaM Unit from do
  let env ← getEnv
  testReelaborate "elab context" env

-- Test 2: importModules (what lake exe would use)
#eval show IO Unit from do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `Lean }] {} (trustLevel := 1024)
  testReelaborate "importModules trustLevel=1024" env

-- Test 3: importModules with loadExts
#eval show IO Unit from do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{ module := `Lean }] {} (trustLevel := 0)
  testReelaborate "importModules loadExts=true" env
