import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 18


variable {α :Type*} [inst: Setoid α]


Statement  (c : Setoid.Equivclass α ) : ∃ z, z ∈  c := by
  obtain ⟨z, hz⟩ := Setoid.exist_quot c
  rw [hz]
  use z
  exact Setoid.mem_quot_self z

NewTheorem Setoid.exist_quot Setoid.mem_quot_self
NewTactic rewrite rw use exact
OnlyTactic obtain rewrite rw use exact
