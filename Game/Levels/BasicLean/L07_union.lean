import Game.Metadata

World "BasicLean"
Level 7

Title "Definition of union."

Statement {α : Type*} (s t : Set α) (x : α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  rw [Set.mem_union]

Conclusion "Level Completed!"
NewTheorem Set.mem_union
