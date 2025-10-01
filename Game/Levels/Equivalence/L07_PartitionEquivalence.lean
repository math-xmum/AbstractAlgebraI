import Game.Metadata

World "Equivalence"

Level 7

Introduction "The following statement shows that a partition induces an equivalence relation.

The equivalence relation is defined as the relation that relates two elements if they belong to the same subset in the partition.
"

variable (α :Type*) (C : Set (Set α)) (H : Setoid.IsPartition C)


Statement (preamble :=
  let r := fun a b => ∃ s, s ∈ C ∧ a ∈ s ∧ b ∈ s
  refine ⟨r,?refl,?symm,?trans⟩
): Setoid α := by
  · Hint "Let's recall the definition of a partition by unfolding it using `unfold Setoid.IsPartition at H`."
    unfold Setoid.IsPartition at H
    Hint "We need to show that for each element a in α, there exists a subset s in C such that a ∈ s. Use `intro a`."
    intro a
    Hint "From {H}, we can obtain the subset s containing {a}. Use `obtain ⟨s, h1, _⟩ := {H}.2 {a}`."
    obtain ⟨s, h1, _⟩ := H.2 a
    Hint "We can now use this subset s as witness for the existential. Use `use s`."
    use s
    Hint (hidden := true) "Now we need to show that s ∈ C and a ∈ s. Use `exact ⟨{h1}.1,{h1}.2,{h1}.2⟩`."
    exact ⟨h1.1,h1.2,h1.2⟩
  · Hint "We need to show that if two elements x and y belong to the same subset in C, then they are related. Use `intro x y hxy`."
    intro x y hxy
    Hint "From {hxy}, we can obtain the subset s ∈ C containing {x} and {y}. Use `obtain ⟨s, h1, h2⟩ := {hxy}`."
    obtain ⟨s, h1, h2⟩ := hxy
    Hint "We can now use this subset s as witness for the existential in {r}. Use `use s`."
    use s
    Hint (hidden := true) "Now we need to show that s ∈ C and x ∈ s and y ∈ s. Use `exact ⟨{h1},{h2}.2,{h2}.1⟩`."
    exact ⟨h1,h2.2,h2.1⟩
  · Hint "We need to show that if two elements x and y belong to the same subset in C, and y and z belong to the same subset in C, then x and z belong to the same subset in C. Use `intro x y z hxy hyz`."
    intro x y z hxy hyz
    Hint "From {hxy} and {hyz}, we can obtain the subsets s and t in C containing {x}, {y}, and {z}. Use `obtain ⟨s, hs1, hs2⟩ := {hxy}` and `obtain ⟨t, ht1, ht2⟩ := {hyz}`."
    obtain ⟨s, hs1, hs2⟩ := hxy
    obtain ⟨t, ht1, ht2⟩ := hyz
    Hint (hidden := true) "Let's recall the definition of a partition by unfolding it using `unfold Setoid.IsPartition at H`."
    unfold Setoid.IsPartition at H
    Hint (hidden := true) "We need to show that s = t. Use `have hst : s = t := by`."
    have hst : s = t := by
      Hint (hidden := true) "Now use the uniqueness of the subset containing {y} to show that s = t. Use `apply ExistsUnique.unique (H.2 y)`."
      apply ExistsUnique.unique (H.2 y)
      Hint (hidden := true) "Now we need to show that s ∈ C and y ∈ s. Use `exact ⟨{hs1},{hs2}.2⟩`."
      exact ⟨hs1,hs2.2⟩
      Hint (hidden := true) "Now we need to show that t ∈ C and y ∈ t. Use `exact ⟨{ht1},{ht2}.1⟩`."
      exact ⟨ht1,ht2.1⟩
    Hint (hidden := true) "Now we can use this subset s as witness for the existential in {r}. Use `use s`."
    use s
    Hint (hidden := true) "Now we need to show that {s} ∈ {C} and x ∈ {s} and z ∈ {s}. Use `split_ands` to split the goal into three subgoals."
    split_ands
    · Hint (hidden := true) "This is straightforward from {hs1}."
      exact hs1
    · Hint (hidden := true) "This is `{hs2}.1`."
      exact hs2.1
    · Hint (hidden := true) "Use `rw [hst]` to rewrite the goal."
      rw [hst]
      Hint (hidden := true) "This is `{ht2}.2`."
      exact ht2.2


Conclusion "Now we have shown that a partition induces an equivalence relation.

It is easy to see that this gives an bijection between partitions of a set and equivalence relations on that set.

Viewing an equivalence relation as a subset of α × α, the subset relation gives a partial order structure on the set of all equivalence relations on α.

One can also define partial ordering on partitions.

Then the above bijection even preserves the order.
This is precisely the theorem `Setoid.Partition.orderIso` in Mathlib.
"

NewTactic all_goals split_ands
NewTheorem ExistsUnique.unique ExistsUnique.exists ExistsUnique.intro
NewDefinition Setoid.Partition.orderIso





/-
Statement (preamble :=
  let r := fun a b => ∃ s, s ∈ C ∧ a ∈ s ∧ b ∈ s
  refine ⟨r,?refl,?symm,?trans⟩
  ): Setoid α := by

-/
