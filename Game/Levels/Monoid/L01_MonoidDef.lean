import Game.Metadata

import Game.Levels.Lemmas.Group

World "Monoid"

Level 1


Introduction "
Let us get familar with the definition of a monoid.

A monoid is a set with a binary operation that is associative and has an identity element.
"

variable {α : Type*} [Monoid α]

Statement :
  (∀ a b c: α, a * b * c= a * (b * c))
   ∧ ∃ e : α, ∀ a : α, a * e = a ∧ e * a = a := by
   Hint (hidden:=true) "Use `constructor` to split the goal into two parts."
   constructor
   · Hint "Use `exact mul_assoc` or `exact Semigroup.mul_assoc`."
     exact mul_assoc
   · Hint "
     In each Monoid, the identity element is denoted by `1`.
     So use `use 1` to provide the identity element."
     use 1
     Hint (hidden:=true) "Now introduce the element `a`. Use `intro a` to do so."
     intro a
     Hint "{a} * 1 = {a} is the theorem called `mul_one` and 1 * {a} = {a} is called `one_mul`"
     Hint (hidden:=true) "Use `simp [mul_one,one_mul]` to prove this."
     simp [mul_one,one_mul]

NewTheorem mul_one one_mul
OnlyTheorem mul_assoc Semigroup.mul_assoc
OnlyTactic rw simp use exact refine intro
