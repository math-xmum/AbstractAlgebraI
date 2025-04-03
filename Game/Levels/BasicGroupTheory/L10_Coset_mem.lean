import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 10

Introduction "
Let H be a subgroup of G.
The subset g • H := {gh | h∈H} for some g∈G is called a left coset of H.

We first prove the simple fact that
x ∈ g • H ↔ g⁻¹ * x ∈ H

The above lemma is called `mem_leftCoset_iff' in Mathlib.
"

open Monoid Group
open scoped Pointwise
open Pointwise



variable {G : Type*} [Group G] {g x:G} {H : Set G}

--instance : HSMul G (Set G) (Set G):=inferInstance

Statement : x ∈ g • H ↔ g⁻¹ * x ∈ H := by
  constructor
  · intro h1
    Hint "Note that x ∈ g • H means ∃ h: G,  h ∈ H ∧  g * h = x. Use `obtain' to obtain the anxiety element h.
    For example, one can use
    `obtain ⟨h, hh1,hh2⟩ := h1'
    "
    obtain ⟨h, hh1,hh2⟩ := h1
    Hint "Use `simp' to clear up {hh2}"
    simp at hh2
    Hint "Rewrite using {hh2}"
    rw [<-hh2]
    Hint "The goal can be cleared by `simp'/`group' and `assumption'"
    simp
    assumption
  · Hint "Intro the assumption."
    intro h1
    Hint " Use `g⁻¹ * x'"
    use g⁻¹*x
    Hint "The goal can be cleared by `simp'/`group' and `assumption'"
    simp
    assumption
