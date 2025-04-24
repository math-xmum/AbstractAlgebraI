import Game.Metadata

World "BasicLean"
Level 5

Title "Containing relation is reflexive."

Statement {α : Type*} (s : Set α) : s ⊆ s := by
  intro x xs
  exact xs

Conclusion "Level Completed!"
