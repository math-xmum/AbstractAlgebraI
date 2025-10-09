import Game.Metadata

import Game.Levels.Lemmas.Group
import Game.Levels.Monoid.L03_LeftInverseEqRightInverse
World "Monoid"

Level 4


Introduction "
An element `b` is an inverse of `a` if `b * a = 1` and `a * c = 1`, i.e. `b` is both left inverse and right inverse of `a`.

Now we are going to prove that the inverse of an element `a` is unique if it exists.
More precisely, if `b` and `c` are inverses of `a`, then `b = c`.
"

variable {α : Type*} [Monoid α] (a b c : α)

Statement (H1 : Inverse a b) (H2 : Inverse a c) : b = c := by
  Hint "To clarify the situation, we can unfold the definitions of `Inverse`."
  unfold Inverse at H1 H2
  Hint "We can use `Monoid.LeftInverse_eq_RightInverse` to rewrite the goal."
  Hint (hidden := true) "Use `apply Monoid.LeftInverse_eq_RightInverse a `."
  apply Monoid.LeftInverse_eq_RightInverse a
  Hint (hidden := true) "Now we can use `exact H1.1` and `exact H2.2` to close the goal."
  exact H1.1
  exact H2.2

OnlyTheorem Monoid.LeftInverse_eq_RightInverse
