import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 9


variable {α :Type*} [inst: Setoid α]


Statement
 (x : α) : x ∈ {y | x ≈ y} := by
   exact Setoid.refl _


NewTheorem Setoid.refl
OnlyTactic rewrite unfold exact
