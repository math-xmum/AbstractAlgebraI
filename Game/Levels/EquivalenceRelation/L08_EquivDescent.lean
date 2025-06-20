import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]

variable (α) in
abbrev Setoid.equivclasses [Setoid α] := Set.range $ Setoid.equivclass (α := α)

lemma Setoid.equivclasses_nonempty (a: Setoid.equivclasses α): a.1.Nonempty := by
  obtain ⟨a,ha ⟩ := a
  obtain ⟨x, hx⟩ := ha
  use x
  simp [<-hx]
  exact Setoid.refl _

Statement (f : α → β) (H: ∀ a b, a ≈ b → f a = f b):
  let fbar :Setoid.equivclasses α → β := fun c => f (Setoid.equivclasses_nonempty c).some
  ∀ x, f x = fbar ⟨Setoid.equivclass x, by simp⟩
  := by
  intro x
  simp [fbar]
  apply H
  let y := Setoid.equivclasses_nonempty ⟨Setoid.equivclass x, by simp⟩ |>.some
  have H2: y ∈ Setoid.equivclass x := Set.Nonempty.some_mem _
  rw [Setoid.mem_equivclass_iff_equiv] at H2
  exact H2



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
