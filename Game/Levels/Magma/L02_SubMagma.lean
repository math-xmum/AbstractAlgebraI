import Game.Metadata

World "Magma"

Level 2

Introduction "Suppose `S` is a subset of a magma `α` such that for all `x` and `y` in `S`, `x * y` is in `S`. Then `S` is a magma with multiplication inherited from `α`."

variable {α : Type*} [H: Mul α]

Statement
  (preamble:=
    apply Mul.mk
    refine fun x y => ⟨x.1 * y.1,?_⟩
  )
 {S : Set α} (H : ∀ {x y}, x ∈ S → y ∈ S → x * y ∈ S) : Mul S := by
  Hint "Use `H` to prove that `x.1 * y.1` is in `S`."
  exact H x.2 y.2

Conclusion "You have proved that the on `S` is an magma inherited from `α`.
We call `S` a submagma of `α`.
"
