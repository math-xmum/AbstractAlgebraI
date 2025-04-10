import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "GroupHomomorphism"

open scoped Pointwise

Level 4

Introduction "
A subgroup N of G is called a normal subgroup if
∀ g n, n ∈ N → g*n*g⁻¹ ∈ N.

We will show that N is normal if and only if the multiplication of any two left cosets is still a left coset.

In this case, the equation (g • N) * (h • N) = (g*h) • N must holds since g*h is in (g • N) * (h • N).
"
variable {G H:Type*} [Group G] (N : Subgroup G)

#check Subgroup.Normal.conj_mem

Statement : N.Normal ↔ ∀ g h : G,  (g • (N :Set G)) * (h • N) = (g * h) • N := by
  Hint "Use constructor to split the statement into two directions."
  constructor
  · Hint "Introduces all the necessary hypotheses and free variables."
    intro H g h
    Hint "To prove to sets equal, we need to prove that an element in one set if and only if it is in the other set.
    We can use the `ext` tactic to rewrite the goal."
    ext x
    Hint "Use constructor to split the statement into two directions."
    constructor
    · Hint "Introduces all the necessary hypotheses and free variables."
      intro hx
      Hint "Apply the `Set.mem_mul_set_iff` rewrite rule at hypothesis `hx` to transform the membership condition in terms of a product of elements from the left and right sets. This will express `hx` as the existence of two elements whose product equals `x`."
      rw [Set.mem_mul_set_iff] at hx
      Hint "Decompose the existential statement `hx` into individual components `a`, `b`, `ha`, `hb`, and `hab`, to extract elements from the cosets `g • ↑N` and `h • ↑N` and establish their product relation.
      One can achieve this by using the `obtain` tactic.
      "
      obtain ⟨a, b, ha, hb,hab⟩ := hx
      Hint "Use `obtain` to destructure the membership condition `ha : a ∈ g • ↑N` into an element `n1` of the subgroup `N` and an equation `g * n1 = a`."
      obtain ⟨n1, hn1, ha : g*n1 = a ⟩ := ha
      Hint "Apply the same technique to destructure the membership condition `hb : b ∈ h • ↑N` into an element `n2` of the subgroup `N` and an equation `h * n2 = b`."
      obtain ⟨n2, hn2, hb : h*n2 = b ⟩ := hb
      Hint "Note that (g*h) *(h⁻¹ * n1 * h * n2).  To clear the existential statement x ∈ (g * h) • N, we can use  Use `h⁻¹ * n1 * h * n2`."
      use (h⁻¹ * n1 * h * n2)
      Hint "Use the `constructor` tactic to split the goal into two separate subgoals."
      constructor
      · Hint "Since n2 ∈ N, it suffices to show that h⁻¹ * n * h ∈ N. One can apply `Subgroup.mul_mem`."
        apply Subgroup.mul_mem  _ _ hn2
        Hint "Now apply the definition of Normal subgroup, but one should rewrite h⁻¹ * n1 * h as  h⁻¹ * n1 * (h⁻¹)⁻¹. One can use `inv_inv`"
        --have hnh : h⁻¹ * n1 * h =  h⁻¹ * n1 * (h⁻¹)⁻¹ := by group
        nth_rw 2 [<-inv_inv h]
        Hint "Apply the `Subgroup.Normal.conj_mem` lemma."
        apply Subgroup.Normal.conj_mem H
        Hint "Now this is exact {hn1}. "
        exact hn1
      · Hint "This is a direct computation by {hab}, {ha}, {hb} following the group law."
        simp [<-hab,<-ha,<-hb];group
    · Hint "Introduce the hypothesis."
      intro H
      Hint "Extract the element n and the assumption n∈N and ghn=x from the hypothesis {H} using the `obtain` tactic."
      obtain ⟨n, hn,hx : g*h*n = x⟩ := H
      Hint "Rewrite the goal using the `Set.mem_mul_set_iff`."
      rw [Set.mem_mul_set_iff]
      Hint "Now figure out what `a` and `b` should be. "
      use g,(h*n)
      Hint "Use constructor to split the goal. "
      constructor
      · Hint "This is easy since g = g * 1."
        use 1
        Hint "Use `aesop` to finish the goal."
        aesop
      · Hint "Use constructor to split the goal."
        constructor
        · Hint "This is easy since h * n = h * n. You also can use aesop."
          use n; aesop
        · Hint "This is more or less {hx}."
          rw [<-hx];group
  · Hint "Introduce the hypothesis."
    intro H
    Hint "Use constructor to split the goal."
    constructor
    Hint "Introduce the variables and hypothesis."
    intro n hn g
    Hint "How about set h = g⁻¹? You can use `specialize` tactic."
    specialize H g (g⁻¹)
    Hint "The goal can be simplified."
    simp at H
    Hint "Here is a tricky point, `g * n * g⁻¹ ∈ N` is different from `g * n * g⁻¹ ∈ ↑N`. The subgroup N of G is more than a subset of G and ↑N = (N : Set G) represents the underlying set of N (via coercion).
    If you simply use `rw [<-H]` it will fail.
    On the other hand, they are not that different.
    You can use
    ` rw [<- SetLike.mem_coe]`
    to reformulate the goal.
    "
    rw [<-SetLike.mem_coe]
    Hint "Now you can rewrite"
    rw [<-H]
    Hint "Now find (a,b)∈ g N × g⁻¹ N so that a*b = g * n * g⁻¹. "
    use (g*n, g⁻¹)
    Hint "Use constructor to split the goal."
    constructor
    · Hint "This is nothing but g*n ∈ g • N and g⁻¹ * 1 ∈ g⁻¹ • N. You can use Set.mem_prod, or just `simp`.  "
      rw [Set.mem_prod]
      Hint "Break down the goal into two separate sub-goals using the `constructor` tactic."
      constructor
      · exact ⟨n,hn,rfl⟩
      · Hint "You need to use `one_mem`."
        exact ⟨1,by simp [Subgroup.one_mem],by simp⟩
    · Hint "This is simple."
      simp


open scoped Pointwise

NewTheorem MonoidHom.mem_ker inv_inv Set.mem_mul_set_iff Subgroup.Normal.conj_mem Subgroup.one_mem Subgroup.mul_mem Set.mem_prod SetLike.mem_coe
OnlyTactic intro «have» apply_fun rw apply exact assumption aesop
