import Game.Metadata

import Game.Levels.Lemmas.Group

World "Magma"

Level 2

open Set

/-
#check {x : ℝ | x > 0 }
#check mul_pos
-/


Introduction "The following statement claims that the set of odd integers is not closed under addition, meaning it does not form an additive magma."

Statement : ¬ Set.isAddMagma {x : ℤ | Odd x} := by
  Hint "We start by unfolding the definition of `isAddMagma` to see what we need to disprove."
  unfold isAddMagma

  Hint "We need to negate the statement that for all integers $x$ and $y$, if both are odd, then their sum is also odd. We can use `push_neg` to move the negation inward."
  push_neg

  Hint "Now we need to find specific odd integers whose sum is not odd. Let's try using $1$ and $1$, as two odd numbers that add up to an even number."
  use 1,1

  Hint "We need to prove that $1$ is odd, $1$ is odd, and $1 + 1 = 2$ is not odd. The `decide` tactic can automatically prove this kind of simple arithmetic fact."
  decide

NewDefinition Set.isAdMagma
OnlyDefinition Set.isAdMagma
OnlyTactic unfold use rw decide push_neg
