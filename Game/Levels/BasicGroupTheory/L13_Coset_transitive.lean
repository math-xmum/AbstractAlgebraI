import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 13

Introduction "
Let H be a subgroup of G.

Every left coset g • H is an H-orbit under the right translation action:
Let x ∈ g • H. If y is also in g • H, then there is an element h ∈ H such that x * h = y.  Since `h = x⁻¹ * y`, it means `x⁻¹ * y ∈ H`.
The reverse direction is also true.
We now prove this.

Later we call this
`Subgroup.mem_coset_iff_diff_mem_subgroup`
"

open Monoid Group
open scoped Pointwise
open Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}


Statement {x y : G} (hx : x ∈ g • (H : Set G)) :  y ∈  g • (H : Set G) ↔  x⁻¹ * y ∈ H := by
  Hint "Use `constructor` to split the goals. "
  constructor
  · intro hy
    Hint "Use `mem_leftCoset_iff` to translate
    x ∈ g • H into g⁻¹ x ∈ H. "
    replace hx :=(mem_leftCoset_iff _).1 hx
    replace hy :=(mem_leftCoset_iff _).1 hy
    Hint "Note that x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y).
    You can use `have
    have hxy :x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group` to establish this claim.
    "
    have hxy :x⁻¹ * y = (g⁻¹ * x)⁻¹ * (g⁻¹ * y) := by group
    Hint "Use {hxy} to rewrite the goal."
    rw [hxy]
    Hint "If `a ∈ H`, `b ∈ H`, then `a⁻¹ * b ∈ H`. This is Subgroup.mem_of_inv_mul_mem"
    apply Subgroup.mem_of_inv_mul_mem hx hy
  · Hint " Since x ∈ g • H, we have g⁻¹ x ∈ H.
    Therefore, that `y = x * (x⁻¹ * y) = g * ((g⁻¹ * x) * (x⁻¹ * y)) ` for some h∈H.  "
    Hint "We start to execute the above argument with `intro hxy`."
    intro hxy
    Hint "Now use `mem_leftCoset_iff` to translate {hx} into g⁻¹ * x ∈ H."
    have hgx : g⁻¹ * x ∈ H := (mem_leftCoset_iff _).1 hx
    Hint "Now use ((g⁻¹*x) * (x⁻¹ *y)) to closed the goal. "
    use ((g⁻¹*x) * (x⁻¹ *y))
    Hint "Use `constructor` to split the Goal"
    constructor
    · Hint "This follows from `Subgroup.mul_mem`, {hxy} and {hgx}."
      exact Subgroup.mul_mem _ hgx hxy
    Hint "This is follows from the group law. Consider to use `group` and `simp` tactic to clear up the goal."
    simp
    group
