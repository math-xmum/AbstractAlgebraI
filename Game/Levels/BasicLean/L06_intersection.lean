import Game.Metadata

World "BasicLean"
Level 6

Title "Definition of intersection."

Introduction "The following statement asserts that an element $x$ belongs to the intersection of sets $s$ and $t$ if and only if $x$ belongs to both sets $s$ and $t$. "

Statement  {α : Type*} (s t : Set α) (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈  t  := by
  Hint "We can directly use the definition of set intersection, which states that $x ∈  s ∩ t$ is equivalent to $x ∈ s$ and  $x \\in t$. Apply the `rw` tactic with `Set.mem_inter_iff`.
  Simply use `rfl` will also work.
  "
  rw [Set.mem_inter_iff]

Conclusion "Level Completed! We unlock the theorem: Set.mem_inter_iff"
NewTheorem Set.mem_inter_iff
