import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]

Statement (c : Setoid.equivclasses α)  (h1 : x ∈ c.1)  (h2 : x ≈ y ) : y ∈ c.1  := by
  obtain ⟨c, z,hz⟩:= c
  simp only [hz] at *
  rw [Setoid.mem_equivclass_iff_equiv] at *
  exact Setoid.trans h1 h2




OnlyTactic rewrite rfl
OnlyTheorem Set.mem_setOf_eq
