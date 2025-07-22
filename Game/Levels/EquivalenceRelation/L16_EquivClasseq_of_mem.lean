import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 16


variable {α :Type*} [inst: Setoid α]

Statement {x : α} {c : Setoid.Equivclass α}  : x ∈ c ↔ c = Setoid.quot x:= by
  obtain ⟨y, hy⟩ := Setoid.exist_quot c
  rw [hy]
  rw [Setoid.mem_quot_iff_equiv]
  symm
  exact Setoid.quot_eq_iff_equiv



OnlyTheorem Setoid.exist_quot Setoid.mem_quot_iff_equiv Setoid.quot_eq_iff_equiv
OnlyTactic rewrite rw rfl obtain  symm exact
