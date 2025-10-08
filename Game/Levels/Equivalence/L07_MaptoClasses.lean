import Game.Metadata

World "Equivalence"

Level 7

variable (α :Type*) (r : Setoid α)

Introduction "
Given an equivalence relation `r` on a type `α`, we have a function `f` that maps each element `a` to the equivalence class of `a` under `r`.

The following statement proves that the preimage of an equivalence class under a function is nothing but the equivalence class itself."

Statement (preamble :=
    have equiv_class_eq : ∀ {a b}, r a b → {x | r x a} = {x | r x b} := ?_
    obtain ⟨s,hs⟩ := s
  ) {s} :
  let f : α → r.classes := fun a => ⟨{x | r x a}, ⟨a,rfl⟩⟩
  f ⁻¹' {s} = s
 := by
    Hint "Note that `{s}` is an equivalence class. So we can obtain an element `a` in `s` such that `{s} = \{x | r x \{a}}`."
    obtain ⟨a,ha⟩ := hs
    Hint "To prove the equality between two sets, we need to show that each element of the left-hand side is in the right-hand side and vice versa.
    Use `ext b` to start the proof."
    ext b
    Hint "Use `simp [{ha},f]` to simplify the expression and unfold the definition of `f`."
    simp [ha,f]
    Hint "We need to prove two implications. Use `constructor` to split the goals."
    constructor
    · Hint "Introduce the hypothesis."
      intro H
      Hint (hidden := true) "Use `Setoid.refl` to prove that `b` is in the equivalence class of `b`.
      Try `have H2 : {b} ∈ \{x | r x {b}} := Setoid.refl _`.
      "
      have H2 : b ∈ {x | r x b} := Setoid.refl _
      Hint (hidden := true) "Use `rw [{H}] at {H2}` to rewrite the hypothesis."
      rw [H] at H2
      Hint (hidden := true) "Use `exact {H2}` to conclude."
      exact H2
    · Hint (hidden := true) "Use `exact {equiv_class_eq}` to conclude."
      exact equiv_class_eq
    Hint "Now we prove the intermediate result: a and b are equivalent, then they have the same equivalence class."
    Hint "First introduce the variable `a` and `b` and the hypothesis `hab`. Use `intro a b hab`."
    intro a b hab
    Hint "Use `ext x` to start the proof."
    ext x
    Hint "Use `constructor` to split the goals."
    constructor
    · Hint "Introduce the hypothesis."
      intro hxa
      Hint (hidden := true) "Use `Setoid.trans` to prove that `x` is in the equivalence class of `b`."
      exact Setoid.trans hxa hab
    Hint "Introduce the hypothesis."
    intro hxb
    Hint (hidden := true) "Use `Setoid.trans` and `Setoid.symm` to prove that `x` is in the equivalence class of `b`."
    exact Setoid.trans hxb (Setoid.symm hab)


Conclusion "Level Completed! There are lots of useful theorems about equivalence relations. Please refer to the library `Mathlib.Data.Setoid.Partition` for more details.

Moreover, in Mathlib, the quotient map `f` is realized as `Quotient` where the domain is a new type. The realization is much more subtle than what we have done here.
We will get back to the point later.
"
