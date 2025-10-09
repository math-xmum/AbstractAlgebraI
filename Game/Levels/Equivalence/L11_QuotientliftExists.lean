import Game.Metadata

World "Equivalence"

Level 11

Introduction "
Let α be a type with an equivalence relation `≈`.
The data is bundled in the class `Setoid α`.

Let `r : Setoid α` be an equivalence relation on `α`.
The collection of all equivalence classes is denoted by `Quotient r` in mathlib.

We have the natural map `Quotient.mk : α → Quotient r` which sends `a : α` to the equivalence class of `a`.

Suppose `f : α → β` is a function such that `f a1 = f a2` if `a1 ≈ a2` then there is a unique function `φ : Quotient α → β` such that `φ ∘ Quotient.mk = f`.

Now we prove the existence of such a function.
Recall that `s : Quotient r → α` is called an section of the quotient map `Quotient.mk` if `Quotient.mk ∘ s` is the identity map on `Quotient r`.

The function `φ` can be defined as `f ∘ s` where `s` is an section of `Quotient.mk`.

"

Statement (α β :Type*) [r : Setoid α] (q : Quotient r) (φ : Quotient r → β) (s : Quotient r → α) (HS :∀ q, ⟦ s q ⟧ = q)
(f : α → β) (H : ∀ {a1 a2}, a1 ≈ a2 → f a1 = f a2)
(φ : Quotient r → β) (H1 : φ =  f ∘ s)
:
 f  = φ ∘ Quotient.mk r
:= by
  Hint "To prove two functions are equal, you can use `ext` to test the function on an element."
  Hint (hidden := true) "Use `ext a` to introduce an element in `{α}`."
  ext a
  Hint "Now apply the definition of `{φ}`."
  Hint (hidden := true) "Use `rw [H1]` to replace `{φ}` with `{f} ∘ {s}`."
  rw [H1]
  Hint "Use `simp` to simplify the goal."
  simp
  Hint "It is the time to apply the hypothesis `{H}`."
  Hint (hidden := true) "Use `apply H` to modify the goal."
  apply H
  Hint "Note that a ≈ b if and only if ⟦a⟧ = ⟦b⟧."
  Hint (hidden := true) "Use `rw [<-Quotient.eq_iff_equiv]` to replace the goal."
  rw [<-Quotient.eq_iff_equiv]
  Hint "It is the time to apply {HS}."
  Hint (hidden := true) "Now we can use `rw [HS]` to replace `⟦{s} ⟦{a}⟧⟧` with `⟦{a}⟧`."
  rw [HS]

NewTheorem Quotient.eq_iff_equiv
