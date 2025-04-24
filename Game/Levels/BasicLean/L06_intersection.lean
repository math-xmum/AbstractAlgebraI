import Game.Metadata

World "BasicLean"
Level 6

Title "Definition of intersection."

Statement {α : Type*} (s t : Set α) (x : α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := by
  rw [Set.mem_inter_iff]

Conclusion "Level Completed!"
NewTheorem Set.mem_inter_iff
