import Game.Metadata


World "Partition"

Level 1

variable {α : Type*} (C : Set (Set α))

Introduction "The following statement shows the definition of a partition of a set (in fact type) α. It states that a collection C of subsets is a partition if it doesn't contain the empty set and every element belongs to exactly one subset in C."

Statement : Setoid.IsPartition C ↔ (∅ ∉ C ∧ ∀ (a : α), ∃! b : Set α, b ∈ C ∧ a ∈ b) := by
  Hint "This is the definition of a partition of a set. Use `rfl` to conclude."
  rfl

OnlyTactic rfl
