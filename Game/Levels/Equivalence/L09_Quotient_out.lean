import Game.Metadata

World "Equivalence"

Level 9

Introduction "
Let α be a type with an equivalence relation `≈`.
The data is bundled in the class `Setoid α`.

Let `r : Setoid α` be an equivalence relation on `α`.
The collection of all equivalence classes is denoted by `Quotient r` in mathlib.

We have the natural map `Quotient.mk : α → Quotient r` which sends `a : α` to the equivalence class of `a`.

A map  `s : Quotient r → α` is called an section of the quotient map `Quotient.mk` if `Quotient.mk ∘ s` is the identity map on `Quotient r`.

In mathlib, a section of `Quotient.mk` is defined using the Axiom of choice,  called `Quotient.out`.
The map send an equivalence class ⟦a⟧ to a fixed choice of its representative, say a' ∈ ⟦a⟧.


We first check that `Quotient.out` is an section.

"

variable (α :Type*) [r : Setoid α] (q : Quotient r) (a :α)

Statement : ⟦q.out⟧ = q:= by
  Hint "This is the theorem `Quotient.out`"
  Hint (hidden := true) "You can use `exact Quotient.out _` or `apply Quotient.out` to close the goal."
  Branch
    exact Quotient.out_eq _
  apply Quotient.out_eq


NewTheorem Quotient.out_eq
