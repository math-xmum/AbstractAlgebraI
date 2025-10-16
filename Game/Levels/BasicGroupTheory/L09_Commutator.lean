import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 9

Introduction "
The expression `⁅a,b⁆:=a * b * a⁻¹ * b⁻¹' is called the commutator of $a$ and $b$.

A group is abelian if all commutators are one.
"


variable {G : Type*} [Group G]

open Group Monoid

Statement {a b: G} : a * b = b * a ↔  a * b * a⁻¹* b⁻¹=1  := by
  Hint "Use `constructor' to split the goal into two parts"
  constructor
  · intro H
    Hint "replace `a * b'  by `b * a' using the hypothesis"
    rw [H]
    Hint "Use `group' to finish the proof"
    group
  · intro H
    Hint "apply `mul_right_cancel' twice to translate the goal"
    apply mul_right_cancel (b := a⁻¹)
    apply mul_right_cancel (b := b⁻¹)
    Hint "Rewrite the left hand side using the hypothesis"
    rw [H]
    Hint "Use `group' to finish the proof"
    group


#check mul_right_cancel

NewTheorem mul_right_cancel mul_left_cancel mul_right_cancel_iff
mul_right_cancel_iff commutatorElement_def
