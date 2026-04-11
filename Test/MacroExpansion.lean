/-
Test: investigate macro expansion in InfoTree — focus on Tree 1 (gen_point_struct).
-/
import Lean

open Lean Elab Command Meta

private def sampleFile := "
import Lean

macro \"gen_point_struct\" name:ident : command =>
  `(structure $name where
      x : Nat
      y : Nat)

gen_point_struct MyPoint

def MyPoint.origin : MyPoint := ⟨0, 0⟩
"

#eval show MetaM Unit from do
  let inputCtx := Parser.mkInputContext sampleFile "<test>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (fileEnv, messages) ← Elab.processHeader header {} messages inputCtx (trustLevel := 1024)
  let cmdState := { Command.mkState fileEnv messages {} with infoState.enabled := true }
  let finalState ← IO.processCommands inputCtx parserState cmdState
  let trees := finalState.commandState.infoState.trees.toArray

  -- Focus on Tree 1 (gen_point_struct MyPoint)
  let tree := trees[1]!
  IO.println "── Tree 1: all info nodes ──"
  let allNodes : Array (String × String) := tree.foldInfo (init := #[]) fun ctx info acc =>
    let tag := match info with
      | .ofCommandInfo _ => "CMD"
      | .ofMacroExpansionInfo _ => "MACRO"
      | .ofTermInfo _ => "TERM"
      | .ofTacticInfo _ => "TACTIC"
      | _ => "OTHER"
    let detail := match info with
      | .ofCommandInfo ci => s!"{ci.stx.getKind}"
      | .ofMacroExpansionInfo mei => s!"in={mei.stx.getKind} → out={mei.output.getKind}"
      | _ => ""
    acc.push (tag, detail)
  IO.println s!"  Total nodes: {allNodes.size}"
  for (tag, detail) in allNodes do
    IO.println s!"  {tag}: {detail}"

  -- Also: try to pretty-print the expanded command from Tree 1
  IO.println "\n── Trying ppCommand on expanded syntax ──"
  -- Walk the tree manually to find MacroExpansionInfo
  let rec walkTree (t : InfoTree) (depth : Nat) : IO Unit := do
    match t with
    | .context _ child => walkTree child (depth + 1)
    | .node info children =>
      match info with
      | .ofMacroExpansionInfo mei =>
        IO.println s!"  [depth={depth}] MACRO: in={mei.stx.getKind} → out={mei.output.getKind}"
        let env := finalState.commandState.env
        let (fmt, _) ← (PrettyPrinter.ppCommand ⟨mei.output⟩).toIO
          { fileName := "<test>", fileMap := default } { env }
        IO.println s!"  ppCommand: {fmt}"
      | .ofCommandInfo ci =>
        IO.println s!"  [depth={depth}] CMD: {ci.stx.getKind}"
      | _ => pure ()
      for child in children do
        walkTree child (depth + 1)
    | .hole _ => pure ()
  walkTree tree 0
