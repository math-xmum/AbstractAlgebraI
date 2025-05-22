import Mathlib
import Qq
import Lean
import Lean.Meta.Tactic.TryThis
import Game.Metadata
import Game.Generator.API


open Lean.Syntax
open Lean Elab Syntax Command Expr
open Qq


/- elab "#testcmd " c:command : command => do
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
 -/



namespace Lean.Syntax

def setArgr (stx: Syntax) (locs: List Nat) (arg: Syntax) : Syntax :=
  match locs with
  | .nil => arg
  | .cons i it => stx.setArg i $ stx[i].setArgr it arg

def setArgsr (stx: Syntax) (locs: List Nat) (args: Array Syntax) : Syntax :=
  match locs with
  | .nil => stx.setArgs args
  | .cons i it => stx.setArg i $ stx[i].setArgsr it args

partial def findall (stx: Syntax) (p: Syntax → Bool) : List Syntax :=
  match stx with
  | stx@(Syntax.node _ _ args) =>
    (if p stx then [stx] else []) ++ args.toList.bind (findall · p)
  | _ => if p stx then [stx] else []

def getProof (stx : Syntax) : Syntax :=
  match stx[1][0].getKind with
  | `lemma      => stx[1][3]
  | `theorem    => stx[1][3]
  | `def => stx[1][3]
  | _ => Syntax.missing

def setProof (stx : Syntax) (newProof : Syntax) : Syntax :=
  match stx[1][0].getKind with
  | `lemma => stx.setArgr [1,3] newProof
  | `theorem     => stx.setArgr [1,3] newProof
  | `def  => stx.setArgr [1,3] newProof
  | _ => stx

def getTacticSeq (stx : Syntax) : Array Syntax :=
  match stx.getKind with
  | `command__Statement____ => stx[6][1][1][0][0].getArgs
  | _ => stx.getProof[1][1][0][0].getArgs

/-- Get the tactic sequence of a proof, excluding the tactic separator.
This is useful for manipulating the tactic sequence. -/
def getTacticSeq' (stx : Syntax) : Array Syntax :=
  let tacSep := stx.getProof[1][1][0][0][1]!
  stx.getProof[1][1][0][0].getArgs.filter (¬ · == tacSep)

def setTacticSeq (stx : Syntax) (tacSeq : Array Syntax) : Syntax :=
  stx.getProof.setArgsr [1,1,0,0] tacSeq

def getProofAfter (stx : Syntax) (pos: String.Pos) : Syntax := Id.run do
  -- let tactic_seq := stx[1][1][3][1][1][0][0].getArgs
  let tactic_seq := stx.getTacticSeq
  let tac_sep := tactic_seq[1]!
  let mut after_seq : Array Syntax := #[]
  for tac in tactic_seq do
    let tac_pos := tac.getPos?.getD 0
    if tac_pos >= pos then
      after_seq := (after_seq.push tac).push tac_sep
  stx.setTacticSeq after_seq

def getProofWithin (stx : Syntax) (pos : String.Pos) (endPos : String.Pos) : Syntax := Id.run do
  let tactic_seq := stx.getTacticSeq
  let tac_sep := tactic_seq[1]!
  let mut within_seq : Array Syntax := #[]
  for tac in tactic_seq do
    let tac_pos := tac.getPos?.getD 0
    if tac_pos >= pos ∧ tac_pos <= endPos then
      within_seq := (within_seq.push tac).push tac_sep
  stx.setTacticSeq within_seq

/-- Push a tactic at the end of a proof -/
def pushTactic (stx : Syntax) (tac : Syntax) : Syntax := Id.run do
  let tactic_seq := stx[1][1][0][0].getArgs
  let tac_sep := tactic_seq[1]!
  let new_seq := (tactic_seq.push tac).push tac_sep
  stx.setArgsr [1,1,0,0] new_seq

def getNearestNoGoalsPos (stx : Syntax) (pos : String.Pos) : String.Pos := Id.run do
  let tactic_seq := stx[1][3][1][1][0][0].getArgs
  let mut nearest_pos := 0
  for tac in tactic_seq do
    let tac_pos := tac.getPos?.getD 0
    if tac_pos > pos then
      break
    nearest_pos := tac_pos
  nearest_pos

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

namespace Analyzer.Process.Cn2Aug

open Lean.Meta


def cn2Aug (stx : Syntax) : CommandElabM <| String := do
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
  let p1 := "I am designing natural language hint for Lean 4 code, as a guidance for beginners to write of Lean tactic and learn mathematics, I will give you the whole proof, after each tactic the comments includes the state before and after applying the tactic. Your task is to out put the annotated proof. Note that you are not allow to make your own judgement of the tactic.

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
If P AND Q is true, then Q AND P is true.
This is actually a statement about the commutativity of conjunction (AND), showing that the order of propositions in a conjunction can be swapped.
 \"
Statement (R :Prop): ∀ (P Q : Prop), P ∧ Q → Q ∧  P  := by
  Hint \"We start by introducing the variables P, Q and the hypothesis h that P ∧ Q is true. You can use `intro`. \"
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
elab "#cn2Aug " c:command : command => do
  elabCommand c
  let statedump ← cn2Aug c.raw
  let prompt := mkPrompt statedump
  --logInfo m!"{prompt}"
  let generationOption : GenerationOptions := {temperature := 0.7, numSamples := 1, «stop» := []}
  let results ← tacticGenerationOpenAI "" [prompt] (← getAPI) generationOption
  logInfo m!"{results}"
  let (hint, _) := results[0]!
  let ref ← getRef
  -- let hint := hint ++ (toString (currentTactic.raw))
  -- logInfo m!"{ref[0]}"
  Command.liftTermElabM $ Tactic.TryThis.addSuggestion ref[0] (hint)

end Analyzer.Process.Cn2Aug

World "abc"
Level 1

#cn2Aug
Statement subset_trans' {α : Type*} (r s t : Set α): r ⊆ s → s ⊆ t → r ⊆ t := by
  intro h₁ h₂ x hx
  apply h₂
  apply h₁
  exact hx


#cn2Aug
theorem and_comm'' (R :Prop): ∀ (P Q : Prop), P ∧ Q → Q ∧ P:= by
   intro P Q h
   constructor
   · exact h.2
   ·
    exact h.1

#cn2Aug
lemma and_comm''' (R :Prop): ∀ (P Q : Prop), P ∧ Q → Q ∧ P:= by
   intro P Q h
   constructor
   · exact h.2
   ·
    exact h.1



Introduction "The following statement claims that subset relation is transitive:
If r is a subset of s, and s is a subset of t, then r is a subset of t."

Statement subset_trans''' {α : Type*} (r s t : Set α): r ⊆ s → s ⊆ t → r ⊆ t := by
  Hint "We start by introducing our hypotheses: h₁ (r ⊆ s), h₂ (s ⊆ t),
  and an arbitrary element x with hypothesis hx that x ∈ r"
  intro h₁ h₂ x hx

  Hint "To show x ∈ t, we can use h₂ which says that any element in s is in t"
  apply h₂

  Hint "Now we need to show x ∈ s, we can use h₁ which says that any element in r is in s"
  apply h₁

  Hint "Finally, we use our hypothesis hx which states that x ∈ r"
  exact hx
