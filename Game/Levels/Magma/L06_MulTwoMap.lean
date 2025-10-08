
import Game.Metadata
import Game.Levels.Lemmas.Group

World "Magma"

Level 6

Introduction "The following statement claims that the function $f(x) = x^2$ (or $x * x$ in Lean notation) is a multiplication homomorphism. In other words, for any two natural numbers $x$ and $y$, $f(x * y) = f(x) * f(y)$."


Statement (preamble:=
  have hf : f = fun x => x * x := rfl
  refine ⟨f,?_⟩
  beta_reduce
  ) :
    let f := fun (x : ℕ) => x * x
    ℕ →ₙ* ℕ
  := by
  Hint "We need to prove that for all natural numbers $x$ and $y$, $(x * y) * (x * y) = (x * x) * (y *y)$. Let's introduce these variables with `intro x y`."
  intro x y

  Hint "We need to simplify the anonymous function applications. Use `simp [hf]`."
  simp [hf]

  Hint "Now we need to manipulate the left side of the equation to match the right side. Let's use the associativity of multiplication. Use `rw [Nat.mul_assoc x y (x * y)]`."
  rw [Nat.mul_assoc x y (x * y)]

  Hint "We can use the commutativity of multiplication to reorder the terms. "
  rw [Nat.mul_comm y (x*y)]

  Hint "Apply associativity again to group the terms properly. "
  rw [Nat.mul_assoc x y y]

  Hint "Finally, we can use associativity one more time to match the right side exactly. "
  rw [<-Nat.mul_assoc x x (y*y)]


OnlyTactic unfold beta_reduce intro rw
NewTheorem Nat.mul_assoc Nat.mul_comm
OnlyTheorem Nat.mul_assoc Nat.mul_comm
NewDefinition Mul.isMulMap
OnlyDefinition Mul.isMulMap
