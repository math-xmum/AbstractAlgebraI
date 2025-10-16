import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 6

Introduction "
Suppose `G` is a group and `a, b ∈ G`.
 Now we show that the equation `a * b = 1 ↔ a = b⁻¹`.
"
open Monoid Group

variable {G :Type*} [Group G]


Statement  {a b :G} : a * b = 1 ↔  a = b⁻¹ := by
  Hint "Use `constructor' to split the goal into two parts"
  constructor
  Hint "Introduce the hypothesis. "
  Hint (hidden := true) "Try `intro H`"
  intro H
  Hint "Observe that `b⁻¹ * b = 1`. "
  Hint (hidden := true) "Try `have H1 : b⁻¹ * b = 1 := inv_mul_cancel b`."
  have H1 : b⁻¹ * b = 1 := inv_mul_cancel b
  Hint "Now rewrite {H} using {H1}."
  Hint (hidden := true) "Try `rw [<-{H1}] at {H}`."
  rw [<-H1] at H
  Hint "Use `mul_right_cancel' to finish the proof."
  Hint (hidden := true) "Try `exact mul_right_cancel {H}`."
  exact mul_right_cancel H
  Hint "Introduce the hypothesis. "
  Hint (hidden := true) "Try `intro H`"
  intro H
  Hint "Rewrite the goal using {H}"
  Hint (hidden := true) "Try `rw [H]`."
  rw [H]
  Hint "Use `inv_mul_cancel'"
  Hint (hidden := true) "Try `exact inv_mul_cancel b`."
  exact inv_mul_cancel b

Conclusion "The theorem just proved is called `mul_eq_one_iff_inv_eq` in Mathlib.
There is a similar theorem  called `mul_eq_one_iff_eq_inv` in Mathlib.
"

NewTheorem mul_eq_one_iff_inv_eq mul_eq_one_iff_eq_inv
OnlyTheorem mul_inv_cancel inv_mul_cancel mul_right_cancel mul_left_cancel
OnlyTactic rw exact «have» intro constructor apply
