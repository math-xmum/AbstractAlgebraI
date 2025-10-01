import Game.Metadata

World "Equivalence"

Level 5


Introduction "The type of all equivalence relation on a type α is bundled as `Setoid α` in mathlib.
Given an equivalence relation `r : Setoid α`, one can use `r a b` or `a ≈ b` to denote `a` and `b` are related by `r`.
Given an element `a : α`, the equivalence class of `a` is the set of all elements that are related to `a` by `r`, i.e. `{b : α | r b a}`.
The set of all equivalence classes of `r` is denoted by `r.classes := { s | ∃ y, s = { x | r x y } }`.

Now we prove that the equivalence classes of a partition of α.
"



variable (α :Type*) (r : Setoid α)

Statement (preamble :=
  have mem_equiv_class: ∀ x, x ∈ {y | r y x} := fun x => ?mem_equiv_class
  refine ⟨? equiv_class_non_empty,?unique_class⟩
  pick_goal 3
  ): Setoid.IsPartition r.classes := by
  · Hint "We need to show that every element is in its own equivalence class. Use `exact Setoid.refl x`."
    exact Setoid.refl x
  · Hint "We need to show that every equivalence class is non-empty. Use `intro H` to introduce the hypothesis."
    intro H
    Hint "We can obtain an element `a` from the equivalence class. Use `obtain ⟨a,ha⟩ := H`."
    obtain ⟨a,ha⟩ := H
    Hint "Now we should prove by contradiction: Observe that `{a}` is in its own equivalence class, i.e. `mem_equiv_class {a}` holds. Use `have H':= mem_equiv_class a` to obtain the claim."
    have H':= mem_equiv_class a
    Hint "We can rewrite the claim using the hypothesis `{ha}`. This gives us `a ∈ ∅`, a contradiction."
    rw [<-ha] at H'
    Hint "Now we can use `contradiction` to conclude."
    contradiction
  · Hint "We need to show that every element is in a uniqueequivalence class. Use `intro a` to introduce an element."
    intro a
    Hint "We now have a candidate for the equivalence class. The equivalent class of `{a}` is the obvious choice, `use \{x | r x {a}}`."
    use {x | r x a}
    Hint "The goal looks messy. We can use `beta_reduce` or `simp` to simplify it."
    beta_reduce
    Hint "Our goal in fact has three parts. Use  `refine ⟨⟨?mem_classes,?mem_class⟩,?unique⟩`"
    refine ⟨⟨?mem_classes,?mem_class⟩,?unique⟩
    · Hint (hidden := true) "We need to show that the set \{x | r x {a}} is in the set of equivalence classes. This is obvious, as \{x | r x {a}} = \{x | r x {a}}. Use `use a` to close the goal."
      use a
    · Hint (hidden := true) "This is just `mem_equiv_class {a}`."
      exact mem_equiv_class a
    · Hint (hidden := true) "We need to show that the equivalence class is unique. Use `intro s ⟨hs1,hac⟩` to introduce the hypothesis."
      intro s ⟨hs,hac⟩
      Hint "The hypothesis `{hs}` is a pair ⟨c,hc⟩, where c in an element of type α  and hc is the claim that {s} = \{x | r x c}.  Use `obtain ⟨c,hc⟩ := hs` to obtain the claim."
      obtain ⟨c,hc⟩ := hs
      Hint "Now we rewrite all {s} by {hc}. Use `rw [hc];rw [hc] at hac`."
      rw [hc]; rw [hc] at hac
      Hint "Now we can use `ext x` to rewrite the goal."
      ext x
      Hint "Now we can use `simp_all` to rephrase the goal."
      simp_all
      Hint "Now we can use `constructor` to split the goal into two parts."
      constructor
      · Hint "Use `intro hxc` to introduce the hypothesis."
        intro hxc
        Hint "Now use `Setoid.trans` and `Setoid.symm`."
        Hint (hidden := true) "Use `exact Setoid.trans hxc (Setoid.symm hac)`."
        exact Setoid.trans hxc (Setoid.symm hac)
      · Hint "Use `intro hxa` to introduce the hypothesis."
        intro hxa
        Hint (hidden := true) "Use `exact Setoid.trans hxa hac`."
        exact Setoid.trans hxa hac


Conclusion "We have shown that the set of equivalence classes form a partition of α.
We unlocked the next theorem: `Setoid.isPartition_classes`."

NewTheorem Setoid.refl Setoid.symm Setoid.trans Setoid.isPartition_classes

NewTactic contradiction use beta_reduce
