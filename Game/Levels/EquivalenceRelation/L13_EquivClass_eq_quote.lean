import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 13


variable {α :Type*} [inst: Setoid α]


Statement (c : Setoid.Equivclass α) : ∃ x, c = Setoid.quot x  := by
  obtain ⟨c, x, hx⟩ := c
  use x
  unfold Setoid.quot
  simp only [hx]

NewDefinition Setoid.quot
NewTactic rewrite
OnlyTactic obtain use unfold rfl simp exact
