
import Mathlib.Dynamics.PeriodicPts
import Mathlib.GroupTheory.OrderOfElement

section order

open Function

variable {α : Type*}  {f : α → α} {x : α} [DecidableEq α]

abbrev peroidAux {x : α} {f : α → α} (h : x ∈ periodicPts f): ℕ :=
Nat.find h



@[to_additive]
abbrev orderOfFintype  [DecidableEq α] [Group α] [Fintype α] (x : α) := Nat.find (⟨Fintype.card α, ⟨Fintype.card_pos_iff.2 ⟨1⟩ ,by exact pow_card_eq_one⟩⟩ : ∃ n, n>0 ∧ x^n = 1)

@[to_additive (attr:=simp) addOrderOfFintype_eq]
lemma orderOfFintype_eq {x : α} [DecidableEq α] [Group α] [Fintype α] : orderOf x = orderOfFintype x := by
  unfold orderOf
  unfold minimalPeriod
  unfold orderOfFintype
  have h : 1 ∈ periodicPts (x * ·) := by sorry
  simp only [h, ↓reduceDite, gt_iff_lt]
  congr
  ext n
  simp
  sorry








lemma aa : addOrderOf (1 : ZMod 4) = 4 := by
  simp
  native_decide









end order
