import Mathlib
import Qq
import Lean

open Lean.Syntax
open Lean Elab Syntax Command
open Qq


elab "#testcmd " c:command : command => do
  let env ← getEnv
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  logInfo "This is the log"
  logInfo c.raw
  logInfo macroRes.get!.1.toString

elab "#testt"  t:stx : command => do
  logInfo "This is a tactic log"
  logInfo t.raw

#testcmd
/--
hahah
-/
lemma aa: ∀ (P Q : Prop), P ∧ Q → P := by
   intro P Q _
   exact h.1

syntax (name := printTacticSequence) "#print_tactic_sequence" : command

@[command_elab printTacticSequence]
def elabPrintTacticSequence : CommandElab

def collectTacticStrings (info : Lean.Elab.InfoTree) : CommandElabM (Array String) := do
  let mut result : Array String := #[]

  match info with
  | Lean.Elab.InfoTree.node info children =>
    if let some tacticInfo := getTacticInfo info then
      result := result.push tacticInfo

    -- Recursively process children
    for child in children do
      let childResults ← collectTacticStrings child
      result := result ++ childResults
  | _ => pure #[]

  return result

def getTacticInfo (info : Lean.Elab.Info) : Option String :=
  match info with
  | Lean.Elab.Info.ofTacticInfo ctx stx _ _ =>
    some (toString stx)
  | _ => none


def ListTactic (stx : Syntax) : CommandElabM <| Array AugmentInfo := do
  let tacSeq := stx.getTacticSeq'.toList




def cn2Aug (stx : Syntax) : CommandElabM <| Array AugmentInfo := do
  let tacSeq := stx.getTacticSeq'.toList
  let opl ← getOpenDecls
  let currNamespace ← getCurrNamespace
  let trees ← getInfoTrees
  let mut newProofs : Array AugmentInfo := #[]
  for tree in trees do
    let bi_enumerator := (List.productTR tacSeq.enum tacSeq.enum).filter fun ((i, _), (j, _)) => i < j
    for ((_, tac1), (_, tac2)) in bi_enumerator do
      let posStart := tac1.getPos?.getD 0
      let posEnd   := tac2.getTailPos?.getD 0
      for g1 in tree.goalsAt? (← getFileMap) posStart do
        for g2 in tree.goalsAt? (← getFileMap) posEnd do
          let goalStart := g1.tacticInfo.goalsBefore.head!
          match g2.tacticInfo.goalsAfter.head? with
          | none              => -- If there are no goals after, we only need to augment the proof
            let name          := Name.mkSimple s!"aug_{posStart}_end"
            let statement     := (g1.ctxInfo.runMetaM {} (withOptions setOptions $ goalToDecl goalStart name))
            let proofAfter    := stx.getProofAfter posStart
            let newProof      := (← statement).raw.setProof proofAfter
            let strProof      := toString $ ← liftCoreM $ ppTactic ⟨newProof⟩
            let strProofF      := toString $ ← liftCoreM $ withOptions setOptions $ ppTactic ⟨newProof⟩
            let strStatement  := toString $ ← liftCoreM $ ppTactic ⟨← statement⟩
            let strStatementF  := toString $ ← liftCoreM $ withOptions setOptions $ ppTactic ⟨← statement⟩
            newProofs := newProofs.push ⟨stx, strStatement, strStatementF, strProof, strProofF, opl.toArray.map toString,
              toString currNamespace, "cn2"⟩
          | some goalAfter    => -- If there are goals after, we need to augment the proof and add a new goal
            let name          := Name.mkSimple s!"aug_{posStart}_{posEnd}"
            try
              let statement   := (g1.ctxInfo.runMetaM {} (withOptions setOptions $ goal2ToDecl goalStart goalAfter name))
              let proofWithin := stx.getProofWithin posStart posEnd
              let addedExact  ← `(tactic | exact $(mkIdent `hg2))
              let proofWithin := proofWithin.pushTactic addedExact.raw
              let newProof    := (← statement).raw.setProof proofWithin
              let strProof   := toString $ ← liftCoreM $ ppTactic ⟨newProof⟩
              let strProofF      := toString $ ← liftCoreM $ withOptions setOptions $ ppTactic ⟨newProof⟩
              let strStatement  := toString $ ← liftCoreM $ ppTactic ⟨← statement⟩
              let strStatementF  := toString $ ← liftCoreM $ withOptions setOptions $ ppTactic ⟨← statement⟩
              newProofs := newProofs.push ⟨stx, strStatement, strStatementF, strProof, strProofF, opl.toArray.map toString,
              toString currNamespace, "cn2"⟩
            catch _ => continue
  return newProofs


elab "#cn2Aug " c:command : command => do
  logInfo c.raw
