import Game.Metadata

World "Equivalence"

Level 10

Introduction "
Let α be a type with an equivalence relation `≈`.
The data is bundled in the class `Setoid α`.

Let `r : Setoid α` be an equivalence relation on `α`.
The collection of all equivalence classes is denoted by `Quotient r` in mathlib.

We have the natural map `Quotient.mk : α → Quotient r` which sends `a : α` to the equivalence class of `a`.

A map  `s : Quotient r → α` is called an section of the quotient map `Quotient.mk` if `Quotient.mk ∘ s` is the identity map on `Quotient r`.

Suppose `f : α → β` is a function such that `f a1 = f a2` if `a1 ≈ a2` to `φ : Quotient α → β`.

The function `φ` is the unique function such that `φ ∘ Quotient.mk = f`, i.e. `φ (⟦ a ⟧) = f a`.

We first show the uniqueness of `φ`.
"
Statement (α β :Type*) [r : Setoid α] (q : Quotient r) (φ ψ : Quotient r → β)
(f : α → β) (H0 : ∀ {a1 a2}, a1 ≈ a2 → f a1 = f a2)
(H1 : ∀ a, φ (⟦ a ⟧) = f a)
(H2 : ∀ a, ψ (⟦ a ⟧) = f a)
: φ = ψ := by
  Hint "To prove two functions are equal, you can use `ext` to test the function on an element."
  Hint (hidden := true) "Use `ext q` to introduce an element in `Quotient r`."
  ext q
  Hint  "Now we choice an element in α such that `q = ⟦ a ⟧`. In fact, `a` can be given by `q.out`.  "
  Hint (hidden := true) "You can use `have H3 : ⟦ {q}.out ⟧ = {q} := Quotient.out_eq {q}` to obtain the fact"
  have H3 : ⟦ q.out ⟧ = q := Quotient.out_eq q
  Hint "Now we can use `rw [{H3}]` to replace `{q}` with `⟦ {q}.out ⟧`."
  rw [<-H3]
  Hint "The goal is now clear by H1 and H2."
  Hint (hidden := true) "You can use `rw [H1 q.out,H2 q.out]` to close the goal."
  rw [H1 q.out,H2 q.out]
