import Informal
open Lean Informal

-- NonUserReason is from Informal.Classify (imported, same project root)
-- But our project root is "Test" since this file is Test/CrossModuleDeps.lean
-- and NonUserReason is in Informal.Classify. Different roots!

-- The real question: in BridgelandStability, the tag file and dep file 
-- share the same root. Let's verify collectDeps logic with a manual check.

#eval show MetaM Unit from do
  let env ← getEnv
  IO.println s!"mainModule: {env.mainModule}"
  IO.println s!"mainModule.getRoot: {env.mainModule.getRoot}"
  
  -- Check NonUserReason
  let idx := env.getModuleIdxFor? `Informal.NonUserReason
  match idx with
  | some i => 
    let modName := env.header.moduleNames[i.toNat]!
    IO.println s!"NonUserReason module: {modName}, root: {modName.getRoot}"
  | none => IO.println "NonUserReason NOT IN MODULE INDEX"

  IO.println "PASS: cross-module dep info"
