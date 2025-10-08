import Game.Metadata

import Game.Levels.Lemmas.Group

World "Monoid"

Level 3


Introduction "Suppose `a`, `b`, and `c` are elements of a monoid `α`.

Suppose `b` is the left inverse of `a` (i.e. `b * a = 1`) and `c` is the right inverse of `a` (i.e. `a * c = 1`).

We are going to prove that `b = c`."


variable {α : Type*} [Monoid α] (a b c : α)

Statement (H1 : LeftInverse a b) (H2 : RightInverse a c) : b = c := by
  Hint "To clarify the situation, we can unfold the definitions of `LeftInverse` and `RightInverse`."
  Hint (hidden := true) "Use `unfold LeftInverse at {H1}` and `unfold RightInverse at {H2}`"
  unfold LeftInverse at H1
  unfold RightInverse at H2
  Hint "To proceed the proof, observe that `b * 1 = b`. This is nothing bth the `mul_one` property."
  Hint (hidden := true) "Use `have H3: b * 1 = b := mul_one b` to establish this fact."
  have H3: b * 1 = b := mul_one b
  Hint "Now we can rewrite `b` as `b * 1`."
  Hint (hidden := true) "Use `rw [<-H3]`."
  rw [<-H3]
  Hint "We can also rewrite `1` as `a * c `."
  Hint (hidden := true) "Use `rw [<-H2]`."
  rw [<-H2]
  Hint "We can rewrite `b * (a * c)` as `(b * a) * c` using the associativity of multiplication."
  Hint (hidden := true) "Use `rw [<-mul_assoc]`."
  rw [<-mul_assoc]
  Hint "We can rewrite `b * a` as `1` using the hypothesis `H1`."
  Hint (hidden := true) "Use `rw [H1]`."
  rw [H1]
  Hint "Finally, we can rewrite `1 * c` as `c` using the `one_mul` property."
  Hint (hidden := true) "Use `rw [one_mul]`."
  rw [one_mul]
