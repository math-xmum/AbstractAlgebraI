import Game.Metadata

World "Equivalence"

Level 5


Introduction "The type of all equivalence relation on a type α is bundled as `Setoid α` in mathlib.
Given an equivalence relation `r : Setoid α`, one can use `r a b` or `a ≈ b` to denote `a` and `b` are related by `r`.
The symbol `≈` can be typed by `\\approx`.
Given an element `a : α`, the equivalence class of `a` is the set of all elements that are related to `a` by `r`, i.e. `{x : α | x ≈ a}`.

We now prove that two equivalence classes `{x | r x a}` and `{x | r x b}`
has non-empty intersection if and only if `a` and `b` are related by `r`.
"



variable (α :Type*) (r : Setoid α) (a b : α)

Statement :
   let Ca := {x | x ≈ a}
   let Cb := {x | x ≈ b}
   have HCa : Ca = {x | x ≈ a} := rfl
   have HCb : Cb = {x | x ≈ b} := rfl
   (Ca ∩ Cb).Nonempty  ↔ a ≈ b := by
   Hint "Use `constructor` to split the proof into two parts."
   constructor
   · Hint "Use `intro H` to introduce the hypothesis."
     intro H
     Hint "
     The set `{Ca} ∩ {Cb}` is non-empty means that there exists an element `x` that is in both `{Ca}` and `{Cb}`.
     Use `obtain ⟨x, hxa, hxb⟩ := H` to obtain the element `x` and the hypotheses `hxa : x ∈ \{x | x ≈ {a}}` and `hxb: x ∈ \{x | x ≈ {b}}`."
     obtain ⟨x, hxa, hxb⟩ := H
     Hint "Use `rw [{HCa}] at {hxa}` and `rw [{HCb}] at {hxb}` to rewrite the hypotheses using the definitions of `{Ca}` and `{Cb}`. )"
     rw [HCa] at hxa
     rw [HCb] at hxb
     Hint "
     One can rewrite the hypotheses {hxa} and {hxb} to `{x} ≈ {a}` and `{x} ≈ {b}` respectively.
     Use `simp at {hxa} {hxb}` or `rw [Set.mem_setOf_eq] at {hxa} {hxb}`"
     rw [Set.mem_setOf_eq] at hxa hxb
     Hint "
     Now the proof follows from the transitivity of `≈`."
     Hint (hidden:=true) "Note that `{x} ≈ {a}` implies `{a} ≈ {x}`. This is because `≈` is symmetric.
     Use `replace {hxa} := Setoid.symm {hxa}` to rewrite `{hxa}` to `{x} ≈ {a}`."
     replace hxa := Setoid.symm hxa
     Hint (hidden:=true) " Now one can use the transitivity of `≈` to conclude that `{a} ≈ {b}`.
     Use `exact Setoid.trans {hxa} {hxb}` to conclude that `{a} ≈ {b}`."
     exact Setoid.trans hxa hxb
   · Hint "Use `intro H` to introduce the hypothesis."
     intro H
     Hint "Now we have to show that there is an element in both `{Ca}` and `{Cb}`."
     Hint (hidden:=true) "
     Clearly, `{a}` is in both `{Ca}` and `{Cb}`.
     Use `use {a}` to choose `{a}` as the witness of the Nonemptyness of `{Ca} ∩ {Cb}`."
     use a
     Hint (hidden:=true) "Now we have to show that `{a} ∈  {Ca} ∩ {Cb}`.
     Use `constructor` to split the proof into two parts. "
     constructor
     · Hint "This is nothing but the reflexivity of `≈`."
       Hint "Use `exact Setoid.refl _` to conclude that `{a} ≈ {a}`."
       exact Setoid.refl _
     . Hint (hidden:=true) "This is nothing but the hypothesis `H`. Use `exact {H}` to conclude. "
       exact H




Conclusion "We have shown that the set of equivalence classes form a partition of α.
We unlocked the next theorem: `Setoid.isPartition_classes`."

NewTheorem Setoid.refl Setoid.symm Setoid.trans Setoid.isPartition_classes

NewTactic contradiction use beta_reduce
