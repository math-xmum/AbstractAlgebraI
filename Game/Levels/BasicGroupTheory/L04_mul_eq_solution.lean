import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 4

Introduction "
Suppose `G` is a group and `a, b ∈ G`.
 Now we show that the equation `a * x = b` has a unique solution.
"
open Monoid Group

variable {G :Type*} [Group G]


Statement (preamble :=
  have h1 : a * (a⁻¹ * b) = b := ?_
  pick_goal 2
 ) {a b :G} : ∃! x,  a * x = b := by
  Hint "We fist show that `a⁻¹ * b` is a solution to `a * x = b`."
  Hint "We can use `mul_assoc`, `mul_inv_cancel`, and `one_mul`."
  Hint (hidden := true) "Try `rw [<-mul_assoc]`,
  `rw [mul_inv_cancel]` then
  `rw [one_mul]`."
  rw [<-mul_assoc]
  rw [mul_inv_cancel]
  rw [one_mul]
  Hint (hidden := true) "Try `use a⁻¹ * b`."
  use a⁻¹ * b
  beta_reduce
  constructor
  exact h1
  intro y hy
  rw  [<-h1] at hy
  exact mul_left_cancel hy





NewTheorem mul_left_cancel mul_right_cancel
