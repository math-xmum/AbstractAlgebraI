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
  have h : 1 ∈ periodicPts (x * ·) := isOfFinOrder_of_finite x
  simp [h]
  congr
  ext n
  simp only [and_congr_right_iff]
  have funn :  (x*·)^[n] = fun y =>  x^n * y := by
    induction n
    · simp;ext;simp
    · simp;
      ext; simp [mul_left_inj,pow_succ]
  unfold IsPeriodicPt
  rw [funn]
  unfold IsFixedPt
  simp










lemma aa : addOrderOf (1 : ZMod 4) = 4 := by
  simp
  native_decide








end order
