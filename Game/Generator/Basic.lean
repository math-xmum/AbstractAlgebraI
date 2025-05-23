import Lean
import GameServer.Commands
-- import Mathlib
import Game.Generator.API
import Lean.Meta.Tactic.TryThis
open Lean Elab Meta Parser PrettyPrinter Tactic

-- def getNextTactic (pos : String.pos) : Syntax :

def mkPrompt (goalBefore currentTactic goalAfter : String) : List String :=
  let p1 := "I am designing natural language hint for Lean 4 code, as a guidance for beginners to write one line of Lean tactic, I will give you state before tactic, state after tactic, and tactic used. Note that you are not allow to make your own judgement of the tactic.

# Example Input
## State before the tactic
x : ℝ
⊢ deriv (fun x => x + 1) x = 1
## Tactic used
rw [deriv_add]
## State after the tactic
x : ℝ
⊢ deriv (fun x => x) x + deriv (fun x => 1) x = 1
case hf
x : ℝ
⊢ DifferentiableAt ℝ (fun x => x) x
case hg
x : ℝ
⊢ DifferentiableAt ℝ (fun x => 1) x
# Example Output
Rewrite deriv_add to distribute the derivation. Note that you will need to show the differentiability for each summand to make this lemma work.

# Your input
## State before the tactic
" ++ goalBefore ++ "
## Tactic used
" ++ currentTactic ++ "
## State after the tactic
" ++ goalAfter
  [p1]

def toSuggestion (hint : String) : TryThis.Suggestion where
  suggestion := s!"Hint \"{hint}\""


open LLMlean


elab "GenerateHint " currentTactic:tactic : tactic => withMainContext do

  let goalBefore ← Tactic.getMainGoal
  logInfo m!"{← ppGoal goalBefore}"
  Tactic.evalTactic currentTactic
  logInfo m!"{currentTactic}"
  let goalAfter ← Tactic.getMainGoal
  logInfo m!"{← ppGoal goalAfter}"
  let prompt := mkPrompt (toString (← ppGoal goalBefore)) (toString currentTactic) (toString (← ppGoal goalAfter))
  logInfo m!"{prompt}"
  let generationOption : GenerationOptions := {temperature := 0.7, numSamples := 1,}
  let results ← tacticGenerationOpenAI prompt (← getAPI) generationOption
  let (hint, _) := results
  let ref ← getRef
  -- let hint := hint ++ (toString (currentTactic.raw))
  -- logInfo m!"{ref[0]}"
  TryThis.addSuggestion ref[0] (toSuggestion hint)
  -- toSuggestion hint



namespace Lean.Syntax


def getProof (stx : Syntax) : Syntax :=
  match stx[1][0].getKind with
  | `lemma      => stx[1][3]
  | `theorem    => stx[1][3]
  | `def => stx[1][3]
  | _ => Syntax.missing

def getTacticSeq (stx : Syntax) : Array Syntax :=
  match stx.getKind with
  | `command__Statement____ => stx[6][1][1][0][0].getArgs
  | _ => stx.getProof[1][1][0][0].getArgs


def getDec (stx : Syntax) : Syntax :=
  match stx.getKind with
  | `command__Statement____ => stx[1]
  | _ => Syntax.missing

def dumpDecl (stx : Syntax) : String:=
  match stx.getKind with
  | `command__Statement____ => s!"{stx[2].prettyPrint} {stx[3].prettyPrint} {stx[5].prettyPrint} := by"
  | _ =>
    match stx[1][0].getKind with
    | `lemma
    | `theorem
    | `def => s!"{stx[1][0].prettyPrint} {stx[1][1].prettyPrint} {stx[1][2].prettyPrint} := by"
    | _ => ""


def toStr (stx : Syntax) : String :=
  match stx.reprint with
  | some a => a
  | none => ""

end Lean.Syntax

namespace HintsGenerator

open Lean.Meta
open Syntax Command Expr

def genhint (stx : Syntax) : CommandElabM <| String := do
  let tacSeq := stx.getTacticSeq.toList
  let mut statedump: String := ""
  statedump := statedump ++ s!"{stx.dumpDecl} := by \n"

  --let opl ← getOpenDecls
  let currNamespace ← getCurrNamespace
  let trees ← getInfoTrees
  logInfo currNamespace
  --logInfo m!"{opl}"
  --logInfo m!"{tacSeq}"
  --let mut newProofs : Array AugmentInfo := #[]
  let padding := " "
  for tree in trees do
    for tac in tacSeq do
      let posStart := tac.getPos?.getD 0
      --let posEnd   := tac.getTailPos?.getD 0
      --logInfo m!"list tactic: {posStart}, {posEnd}, {tac}"
      for g in tree.goalsAt? (← getFileMap) posStart  do
        let ggB ← g.ctxInfo.ppGoals g.tacticInfo.goalsBefore
        let ggA ← g.ctxInfo.ppGoals g.tacticInfo.goalsAfter
        statedump := statedump ++ padding ++  s!"/-\n===Goal Before=== {toString ggB}\n"
        statedump := statedump ++ s!"===Goal After=== {toString ggA}-/\n"
        --logInfo m!"goal Before: {ggB}"
        --logInfo m!"tactic : {tac}"
        --logInfo m!"goal After: {ggA}"
        --let goalStart := g.tacticInfo.goalsBefore.head!
        --let firstgoal:= ← g.ctxInfo.runMetaM {} (Meta.ppGoal goalStart)
        --logInfo m!"first goal Before: {firstgoal}"
        --let goalEnd := g.tacticInfo.goalsAfter.head!
        --let goalAfter:= ← g.ctxInfo.runMetaM {} (Meta.ppGoal goalEnd)
        --logInfo m!"first goal After: {goalAfter}"
      statedump := statedump ++ padding ++ (s!"{tac.toStr}")
  return statedump


def mkPrompt (statedump:String) : String :=
  let p1 := "I am designing natural language hint for Lean 4 code, as a guidance for beginners to write of Lean tactic and learn mathematics, I will give you the whole proof, after each tactic the comments includes the state before and after applying the tactic. Your task is to out put the annotated proof.

  # Output convention
  1. You are not allow to make your own judgement of the tactic.
  2. Use $ $ to embrace the inline math mode.
  3. Use unicode for math symbol when possible
  4. Use \\\\ for latex marcos
  4. The variables/hypothesis name occurred
    before `⊢` should be embraced by curly brackets { }.
    For example, given
    ===Goal Before===
    R : Prop ⊢ ∀ (P Q : Prop), P ∧ Q → Q ∧ P

    The variable R should be embraced by {R}.
    But variable P and Q should not be embraced.


# Example Input
Statement and_comm  (R :Prop): ∀ (P Q : Prop), P ∧ Q → Q ∧  P  := by
 /-
===Goal Before===
R : Prop ⊢ ∀ (P Q : Prop), P ∧ Q → Q ∧ P
===Goal After===
R P Q : Prop h : P ∧ Q ⊢ Q ∧ P-/
 intro P Q h
    /-
===Goal Before===
R P Q : Prop h : P ∧ Q ⊢ Q ∧ P
===Goal After===
case left
R P Q : Prop
h : P ∧ Q
⊢ Q
case right R P Q : Prop h : P ∧ Q ⊢ P-/
 constructor
    /-
===Goal Before===
case left
R P Q : Prop
h : P ∧ Q
⊢ Q
case right R P Q : Prop h : P ∧ Q ⊢ P
===Goal After===
case left R P Q : Prop h : P ∧ Q ⊢ Q-/
 · exact h.2
    /-
===Goal Before===
case right R P Q : Prop h : P ∧ Q ⊢ P
===Goal After===
case right R P Q : Prop h : P ∧ Q ⊢ P-/
 ·
    exact h.1

# Example Output
Introduction \"The following statement claims
If $P$ AND $Q$ is true, then $Q$ AND $P$ is true.
This is actually a statement about the commutativity of conjunction AND, showing that the order of propositions in a conjunction can be swapped.
 \"
Statement (R :Prop): ∀ (P Q : Prop), P ∧ Q → Q ∧  P  := by
  Hint \" {R} is a proposition we never use.
  We start by introducing the variables P, Q and the hypothesis h that P ∧ Q is true. You can use `intro`. \"
  intro P Q h
  Hint \"To prove Q ∧ P, we need to prove both Q and P separately. You can use `constructor` \"
  constructor
  Hint \"For the left goal (Q), we can use the right part (second component) of our hypothesis {h}: P ∧ Q. You can use `exact {h}.2\"
  · exact h.2
  Hint \"For the right goal (P), we can use the left part (first component) of our hypothesis {h}: P ∧ Q\"
  · exact h.1

# Your input" ++ statedump
  p1

open LLMlean
elab "#Genhint " c:command : command => do
  elabCommand c
  let statedump ← genhint c.raw
  let prompt := mkPrompt statedump
  logInfo m!"{prompt}"
  let generationOption : GenerationOptions := {temperature := 0.7, numSamples := 1}
  let results ← tacticGenerationOpenAI [prompt] (← getAPI) generationOption
  --logInfo m!"{results}"
  let (hint, _) := results
  let ref ← getRef
  -- let hint := hint ++ (toString (currentTactic.raw))
  -- logInfo m!"{ref[0]}"
  Command.liftTermElabM $ Tactic.TryThis.addSuggestion ref[0] (hint)

end HintsGenerator
