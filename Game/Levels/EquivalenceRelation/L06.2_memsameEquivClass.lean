import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]


Statement (c : Setoid.equivclasses α): x ∈ c.1 ∧ y ∈ c.1  → x ≈ y := by
  obtain ⟨c, z,hz⟩:= c
  simp only [hz]
  rintro ⟨hx,hy⟩
  rw [Setoid.mem_equivclass_iff_equiv] at *
  exact Setoid.trans (Setoid.symm hx) hy




OnlyTactic rewrite rfl
OnlyTheorem Set.mem_setOf_eq
