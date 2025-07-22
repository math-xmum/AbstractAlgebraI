import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 8


variable {α :Type*} [Setoid α]


Statement {x y z : α} (H : x ≈ y) : x ≈ z ↔ y ≈ z := by
  constructor
  intro H2
  exact Setoid.trans (Setoid.symm H) H2
  intro H2
  exact Setoid.trans H H2

NewTheorem Setoid.symm Setoid.trans
NewTactic «intro» rfl rw exact unfold constructor
OnlyTactic intro rfl rw exact unfold constructor
