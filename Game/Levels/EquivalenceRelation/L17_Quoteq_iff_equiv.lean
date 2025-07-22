import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 17


variable {α :Type*} [inst: Setoid α]

Statement {x y: α} : Setoid.quot x = Setoid.quot y ↔ x ≈ y := by
  simp [Setoid.equivclass_eq_iff_equiv (α := α)]



NewTheorem Setoid.equivclass_eq_iff_equiv
OnlyTheorem Setoid.equivclass_eq_iff_equiv
OnlyTactic simp rw
