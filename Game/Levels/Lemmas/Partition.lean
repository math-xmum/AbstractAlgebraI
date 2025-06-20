import Mathlib.Order.SetNotation
import Mathlib.Init.Logic
import Mathlib.Init.Set
import Mathlib.Data.Set.Basic


/-- A collection `c : Set (Set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def IsPartition (c : Set (Set α)) := ∅ ∉ c ∧ ∀ a, ∃! b, b ∈ c ∧ a ∈ b

def IsPartition' (c : Set (Set α)) := ∅ ∉ c ∧ ( ⋃₀ c = Set.univ) ∧ ( ∀ a ∈ c,  ∀ b ∈ c, a ∩ b ≠ ∅ → a = b)

#print IsPartition'


namespace Setoid
variable {α :Type*} [inst: Setoid α]

abbrev equivclass (x : α):  Set α := {y | x ≈ y}

lemma mem_selfequivclass (x : α) : x ∈ Setoid.equivclass x  := by
   rewrite [Set.mem_setOf_eq]
   exact Setoid.refl _


lemma mem_equivclass_iff_equiv (x : α): y ∈ Setoid.equivclass x ↔ x ≈ y := by
  rewrite [Set.mem_setOf_eq]
  rfl


lemma equivclass_eq_iff_equiv  (x y: α): Setoid.equivclass x = Setoid.equivclass y ↔ x ≈ y := by
  constructor <;> intro H
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


lemma equivclass_nonempty (x : α) : Setoid.equivclass x ≠ ∅ := by
  rw [ne_eq]
  intro h
  apply Set.not_mem_empty x
  rw [<-h, Set.mem_setOf_eq]
  exact Setoid.refl _


end Setoid
