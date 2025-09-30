import Game.Metadata


World "Partition"

Level 3


variable {α β: Type*} (f: α → β)

Introduction "The following statement proves that the fiber of a function is a partition of the domain of the function."

Statement Function.fiber_partition (f: α → β) : Setoid.IsPartition $ Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val}) := by
  Hint "Use `constructor` to separate the two parts of the definition of a partition."
  constructor
  · Hint "Use `rw [Set.mem_range]` rephrase the goal."
    rw [Set.mem_range]
    Hint "Use `intro` to introduce the hypothesis."
    intro H
    Hint "Use `obtain ⟨y,hy⟩ := H` to decompose the hypothesis {H} into y and a hypothesis hy."
    obtain ⟨y, hy⟩ := H
    Hint "Use `obtain ⟨x, hx⟩ := y.2` to decompose the hypothesis y into x and a hypothesis hx."
    obtain ⟨x, hx⟩ := y.2
    Hint "Use `have hx': x ∈ f ⁻¹' {y}.val := {hx}` to introduce a hypothesis hx'."
    have hx': x ∈ f ⁻¹' {y.val} := hx
    Hint (hidden := true) "Use `rw [hy] at hx'` to rewrite the hypothesis hx' using the hypothesis hy."
    rw [hy] at hx'
    Hint (hidden := true) "Use `rw [Set.mem_empty_iff_false] at hx'` to rewrite the hypothesis hx' using the hypothesis hy."
    rw [Set.mem_empty_iff_false] at hx'
    Hint (hidden := true) "Use `exact hx'` to conclude."
    exact hx'
  · Hint "Use `intro` to introduce an element a in α "
    intro a
    Hint "Use `use (f ⁻¹' \{f a})` to introduce a set in the partition."
    use (f ⁻¹' {f a})
    Hint "Use `simp` to simplify the goal."
    simp
    Hint (hidden := true) "Use `intro` to introduce an element b in β."
    intro b
    Hint (hidden := true) "Use `intro` to introduce a hypothesis H."
    intro H
    Hint (hidden := true) "Use `ext` to rewrite the goal."
    ext x
    Hint (hidden := true) "Use `rw [H]` to rewrite the goal."
    rw [H]

Conclusion "Level Completed! We unlock the following theorem: Function.fiber_partition"

NewTactic constructor intro obtain ext rw exact simp use
NewTheorem Set.mem_range Set.mem_empty_iff_false
NewTheorem Function.fiber_partition
