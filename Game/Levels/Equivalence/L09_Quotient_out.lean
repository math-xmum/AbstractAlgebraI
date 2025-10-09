import Game.Metadata

World "Equivalence"

Level 8

Introduction "
Let α be a type with an equivalence relation `≈`.
The data is bundled in the class `Setoid α`.

Now the collection of all equivalence classes is denoted by `Quotient α` in mathlib.

We have the natural map `Quotient.mk : α → Quotient α` which sends `a : α` to the equivalence class of `a`.

A map  `s : Quotient α → α` is called an section of the quotient map `Quotient.mk` if `Quotient.mk ∘ s` is the identity map on `Quotient α`.

In mathlib, a section of `Quotient.mk` is defined using the Axiom of choice,  called `Quotient.out`
"

variable (α :Type*) [Setoid α] (a : α)

Statement : ⟦ (⟦ a ⟧).out ⟧ = ⟦ a ⟧ := by
  apply Quotient.out_eq
