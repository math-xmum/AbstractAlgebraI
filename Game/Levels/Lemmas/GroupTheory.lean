import Mathlib.Tactic

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Deprecated.Subgroup

section Subgroup
variable {G : Type*} [Group G] {H : Subgroup G} {a b g: G}
open scoped Pointwise
open Pointwise

/--
If `H` is a subgroup of `G`, `a ∈ H` and `b ∈ H`, then `a⁻¹ * b ∈ H`.
-/
lemma Subgroup.mem_of_inv_mul_mem  (ha : a ∈ H) (hb : b ∈ H) : a⁻¹ * b ∈ H := by
  replace ha : a⁻¹ ∈ H := Subgroup.inv_mem _ ha
  exact Subgroup.mul_mem _ ha hb


/--
If `H` is a subgroup of `G`, `a ∈ H` and `b ∈ H`, then `a * b⁻¹ ∈ H`.
-/
lemma Subgroup.mem_of_mem_mul_inv (ha : a ∈ H) (hb : b ∈ H) :  a * b⁻¹ ∈ H := by
  replace hb : b⁻¹ ∈ H := Subgroup.inv_mem _ hb
  exact Subgroup.mul_mem _ ha hb

/--
For any x ∈ g • H, we have  y ∈ g • H ↔ x⁻¹ * y ∈ H.
-/
lemma Subgroup.mem_coset_iff_diff_mem_subgroup (hx : x ∈ g • (H : Set G)) :  y ∈  g • (H : Set G) ↔  x⁻¹ * y ∈ H := by
  constructor
  · intro hy
    replace hx :=(mem_leftCoset_iff _).1 hx
    replace hy :=(mem_leftCoset_iff _).1 hy
    have hxy :x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group
    rw [hxy]
    apply Subgroup.mem_of_inv_mul_mem hx hy
  · intro hxy
    have hgx : g⁻¹ * x ∈ H := (mem_leftCoset_iff _).1 hx
    use ((g⁻¹*x) * (x⁻¹ *y))
    constructor
    · exact Subgroup.mul_mem _ hgx hxy
    simp; group


end Subgroup
