import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 3

Introduction " The goal of this level is to prove `b = c` from `a * b = a * c`.
This is rule is called the cancelation law.
"
open Monoid Group

variable {G :Type*} [Group G] {H: Set G}


Statement {a b c:G} (h1 : a * b = a * c) : b = c := by
  Hint "We can use `apply_fun` to apply a function to both sides of an equation.
  Here we apply the function `a⁻¹ * ·` to both sides of `{h1}`.
  This is equivalent to multiplying both sides of `{h1}` by `a⁻¹` on the left.
  "
  Hint (hidden := true) "Try `apply_fun (a⁻¹ * · ) at {h1}`."
  apply_fun (a⁻¹ * · ) at h1
  Hint "Now we can use `mul_assoc` twice to rewrite the equation."
  Hint (hidden := true) "Try `rw [<-mul_assoc] at {h1}` twice. Or use `repeat rw [<-mul_assoc] at {h1}`."
  Branch
    repeat rw [<-mul_assoc] at h1
  rw [<-mul_assoc] at h1
  rw [<-mul_assoc] at h1
  Hint "Now we can use `inv_mul_cancel` to rewrite the equation."
  Hint (hidden := true) "Try `rw [inv_mul_cancel] at {h1}`."
  rw [inv_mul_cancel] at h1
  Hint "Now we can use `one_mul` twice to rewrite the equation."
  Hint (hidden := true) "Try `rw [one_mul] at {h1}` twice. Or use `repeat rw [one_mul] at {h1}`."
  Branch
    repeat rw [one_mul] at h1
  rw [one_mul] at h1
  rw [one_mul] at h1
  Hint "Now we can use `{h1}` to finish the proof."
  exact h1

Conclusion "Now you have used the theorem `inv_mul_cancel` and `mul_inv_cancel` in this level. The theorem we proved in this level is called `mul_left_cancel`.
We also have similar theorem called `mul_right_cancel`.
"

NewTheorem mul_one one_mul mul_inv_cancel inv_mul_cancel
