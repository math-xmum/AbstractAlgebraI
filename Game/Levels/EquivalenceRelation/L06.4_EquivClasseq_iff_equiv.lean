import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]


Statement (preamble := constructor <;> intro H) (x y: α): Setoid.equivclass x = Setoid.equivclass y ↔ x ≈ y := by
  have hy := Setoid.mem_selfequivclass y
  rw [<-H] at hy
  rw [Setoid.mem_equivclass_iff_equiv] at hy
  exact hy
  ext z
  repeat rw [Setoid.mem_equivclass_iff_equiv]
  constructor
  intro H1
  replace H := Setoid.symm H
  exact Setoid.trans H H1
  intro H1
  exact Setoid.trans H H1

OnlyTactic rewrite rfl
OnlyTheorem Set.mem_setOf_eq
