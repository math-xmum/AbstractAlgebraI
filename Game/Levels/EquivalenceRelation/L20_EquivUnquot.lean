import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 20


variable {α :Type*} [inst: Setoid α]


Statement (c : Setoid.Equivclass α) : Setoid.quot c.unquot = c := by
  symm
  rw [<-Setoid.mem_quot_iff_eq_quot]
  exact c.unquot_mem


NewTheorem Setoid.Equivclass.unquot_mem Setoid.mem_quot_iff_eq_quot
