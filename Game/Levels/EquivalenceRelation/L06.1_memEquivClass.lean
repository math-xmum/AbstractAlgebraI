import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]


Statement (x : α): y ∈ Setoid.equivclass x ↔ x ≈ y := by
  rewrite [Set.mem_setOf_eq]
  rfl

OnlyTactic rewrite rfl
OnlyTheorem Set.mem_setOf_eq
