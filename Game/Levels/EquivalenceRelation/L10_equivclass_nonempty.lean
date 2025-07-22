import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 10


variable {α :Type*} [inst: Setoid α]

Statement (x : α) : {y | x ≈ y} ≠ ∅ := by
  push_neg
  use x
  simp only [Set.mem_setOf_eq]
  rfl


NewTheorem Set.mem_setOf_eq
NewTactic push_neg use simp rfl apply rw
OnlyTactic push_neg use simp rfl apply rw
