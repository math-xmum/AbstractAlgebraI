import Game.Metadata

import Game.Levels.Lemmas.Group

World "Magma"

Level 7

Introduction "We show that subtraction is not commutative."

Statement : ¬ Std.Commutative (fun (x y : ℤ) => x-y ) := by
  Hint "Suppose sub is commutative. Then we have a contradiction."
  intro H
  Hint "We can use `H.comm 2 1` to get $2-1 = 1-2$ from the commutativity."
  replace H := H.comm 2 1
  Hint "But his is an obvious contradiction. Use `contradiction` to finish the proof."
  contradiction

OnlyTactic intro «have» replace contradiction
