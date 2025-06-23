import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]

variable (α) in
abbrev Setoid.equivclasses [Setoid α] := {c : Set α // ∃ x, c =  Setoid.equivclass x }


lemma Setoid.equivclasses_nonempty (a: Setoid.equivclasses α): a.1.Nonempty := by
  obtain ⟨a,ha ⟩ := a
  obtain ⟨x, hx⟩ := ha
  use x
  simp only [hx]
  exact Setoid.refl _

abbrev Setoid.quot: α → Setoid.equivclasses α := fun x => ⟨Setoid.equivclass x, ⟨x,rfl⟩⟩

noncomputable abbrev Setoid.equivclasses.unquot : Setoid.equivclasses α → α :=  fun c => (Setoid.equivclasses_nonempty c).some

variable (c : Setoid.equivclasses α)

Statement : Setoid.quot c.unquot = c := by


/-
variable {α :Type*} (r : Equivelance α)


Statement (preamble := refine ⟨?nonempty , ?union_eq_univ , ?inter_implies_equal⟩ ): IsPartition' <| Setoid.equivclass '' (Set.univ : Set α)  := by
  simp [Setoid.equivclass_nonempty]
  rw [Set.image_univ, Set.sUnion_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [Set.mem_iUnion]
  use x
  exact Setoid.mem_selfequivclass _
  intro a ha b hb
  obtain ⟨x,_,hx⟩ := ha
  obtain ⟨y,_,hy⟩ := hb
  intro hab
  push_neg at hab
  obtain ⟨z, haz,hbz⟩:= hab
  rw [<-hx] at *
  rw [Setoid.mem_equivclass_iff_equiv] at haz
  rw [<-hy] at *
  rw [Setoid.mem_equivclass_iff_equiv] at hbz
  rw [hx]
  rw [Setoid.equivclass_eq_iff_equiv]
  apply Setoid.trans haz
  exact Setoid.symm hbz
abbrev Equivalence.equivclass : α → Set α := fun x => {y | r x y}
Statement (preamble := constructor): IsPartition <| equivclass r '' Set.univ  := by
-/

NewTheorem Setoid.equivclass_nonempty
