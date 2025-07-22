import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 21


variable {α :Type*} [inst: Setoid α] (c : Setoid.Equivclass α)


Statement (x : α) : x ≈ (Setoid.quot x).unquot := by
  rw [<-Setoid.quot_eq_iff_equiv]
  rw [Setoid.Equivclass.quot_unquot_eq]


NewTheorem Setoid.Equivclass.unquot_mem Setoid.mem_quot_iff_eq_quot Setoid.Equivclass.quot_unquot_eq
