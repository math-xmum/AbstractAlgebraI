import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 5

Introduction "
Suppose `G` is a group and `a, b ∈ G`.
 Now we show that the equation `(a * b)⁻¹ = b⁻¹ * a⁻¹`.
"
open Monoid Group

variable {G :Type*} [Group G]


Statement (preamble :=
  have h0 : (a *b ) * (a * b)⁻¹ = 1 := mul_inv_cancel _
  have h1 : a * b* (b⁻¹ * a⁻¹) = 1 := ?eq_one
  pick_goal 2
 ) {a b :G} :(a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  Hint "On the other hand, we have (a * b) * (a * b)⁻¹ = 1) by the definition of inverse. This is {h0}"
  Hint "We first observe that `a * b * (b⁻¹ * a⁻¹)` is equal to `1`. "
  Hint "We can use `mul_assoc`, `mul_inv_cancel` and `one_mul`."
  Hint (hidden := true) "Try `rw [mul_assoc]`."
  rw [mul_assoc]
  Hint (hidden := true) "Try `rw [<-mul_assoc b]`."
  rw [<-mul_assoc b]
  Hint (hidden := true) "Try `rw [mul_inv_cancel]`."
  rw [mul_inv_cancel]
  Hint (hidden := true) "Try `rw [one_mul]`."
  rw [one_mul]
  Hint (hidden := true) "Try `rw [mul_inv_cancel]`"
  rw [mul_inv_cancel]
  Hint "Now we have `(a * b) * (a * b)⁻¹ = (a * b) * (b⁻¹ * a⁻¹) `"
  Hint (hidden := true) "Try `rw [<-h1]` at h0."
  rw [<-h1] at h0
  Hint "Now we can use `mul_left_cancel` to finish the proof."
  Hint (hidden := true) "Try `exact mul_left_cancel {h0}`."
  exact mul_left_cancel h0

Conclusion "In Mathlib, the theorem we just proved is called `mul_inv_rev`.
"

NewTheorem mul_inv_rev
