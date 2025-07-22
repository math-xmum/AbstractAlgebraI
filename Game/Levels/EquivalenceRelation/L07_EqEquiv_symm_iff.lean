import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 7


variable {α :Type*} [Setoid α]


Statement {x y : α} : x ≈ y ↔ y ≈ x := by
  constructor
  exact Setoid.symm
  exact Setoid.symm


NewTheorem Setoid.symm
NewTactic «intro» rfl rw exact unfold constructor
OnlyTactic intro rfl rw exact unfold constructor
