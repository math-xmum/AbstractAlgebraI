import Game.Metadata


World "Magma"

Level 9

Introduction "We show that matrix multiplication is not commutative."

--#eval !![0,1;0,0]*!![0,0;1,0]
--#eval !![0,0;1,0]*!![0,1;0,0]

Statement : ¬ Std.Commutative (fun (x y : Matrix (Fin 2) (Fin 2) ℤ) => x * y ) := by
  Hint "Suppose multiplication is commutative. Then we have a contradiction."
  intro H
  Hint "We can use `H.comm !![0,1;0,0] !![0,0;1,0]` to get $!![1,0;0,1] = !![0,0;0,0]$ from the commutativity."
  replace H := H.comm !![0,1;0,0] !![0,0;1,0]
  Hint "But his is an obvious contradiction. Use `contradiction` to finish the proof."
  contradiction

OnlyTactic intro «have» replace contradiction
