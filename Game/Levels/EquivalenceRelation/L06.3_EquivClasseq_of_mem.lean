import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]


Statement  (x : α) (c : Setoid.equivclasses α)  (H : x ∈ c.1) : Setoid.equivclass x = c.1:= by
  ext z
  rw [Setoid.mem_equivclass_iff_equiv]
  constructor
  intro H2
  exact Setoid.mem_equivclass_of_equiv H H2
  intro H2
  exact Setoid.equiv_of_mem_sameclass H H2

OnlyTactic rewrite rfl
OnlyTheorem Set.mem_setOf_eq
