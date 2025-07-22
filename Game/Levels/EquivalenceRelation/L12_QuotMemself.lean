import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 12


variable {α :Type*} [inst: Setoid α]


Statement
 (x : α) : x ∈ Setoid.quot x  := by
   unfold Setoid.quot
   exact Setoid.refl _


NewDefinition Setoid.quot
NewTheorem Setoid.refl
NewTactic unfold
OnlyTactic rewrite unfold exact
