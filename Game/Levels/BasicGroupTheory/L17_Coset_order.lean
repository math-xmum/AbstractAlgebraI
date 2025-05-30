import Game.Metadata

World "BasicGroupTheory"

Level 17

Introduction "
Let H be a subgroup of G.
The set of all left cosets of H is denoted by
G/H:= {g • H | g ∈ G}.

The cardinality of G/H is called the index of H in G.
Note that there is a natural surjection π : G → G/H given by g ↦ gH. Then the fiber π(gH) is gH. We have shown that gH and g'H have a bijection between then. In particular
|G| = |G/H| * |H|. This is called the Lagrange theorem.

In particular, the order of any subgroup is a divisor of the order of the group (when the group is finite).



"

open Monoid Group
open scoped Pointwise

variable {G : Type*} [Group G] {g :G} {H : Subgroup G}

open Pointwise

Statement  (g k : G) :
  (g • H :Set G) ∩ (k • H : Set G) = ∅ ∨  (g • H :Set G) = (k • H : Set G) := by
  Hint "By classical logic, P ∨ Q is equivalent to ¬ P → Q.
  Rewrite using `Classical.or_iff_not_imp_left` to translate the goal into ¬ P → Q. "
  rw [Classical.or_iff_not_imp_left]
  Hint "Now introduce a hypothesis `hypo : ¬ (g • H :Set G) = (k • H : Set G)`"
  intro hypo
  push_neg at hypo
  obtain ⟨x,hx1,hx2⟩ := hypo
  ext z
  Hint "By `Subgroup.mem_coset_iff_diff_mem_subgroup`, z ∈ g • H ↔ z⁻¹ * x ∈ H. One can use rewrite to replace z ∈ g • H with z⁻¹ * x ∈ H. "
  rw [Subgroup.mem_coset_iff_diff_mem_subgroup hx1]
  Hint "Do the same thing for z ∈ k • H. If you use `rw` The goal is automatically closed since `rw` all rewrite the goal and then apply `rfl`. If you wish to prevent this, you can use the tactic `rewrite` instead."
  rewrite [Subgroup.mem_coset_iff_diff_mem_subgroup hx2]
  rfl

NewTactic rewrite push_neg
NewTheorem Classical.or_iff_not_imp_left Classical.or_iff_not_imp_right Subgroup.mem_coset_iff_diff_mem_subgroup
