import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 7

Introduction "
A subgroup of a group $G$ is a nonempty subset $H$ of $G$ such that $*$ is closed under $H$ and inverse.

We have a criterion for a set H to be a subgroup of $G$:
If H is non-empty and a ∈  H ∧ b ∈  H implies a * b⁻¹ ∈ H
then H is a subgroup of G

The follow theorem this criterion.
"
open Monoid Group

variable {G :Type*} [Group G] {H: Set G}

abbrev IsSubgroup (H : Set G) :=  H.Nonempty ∧ (∀ {a:G}, a∈H → a⁻¹∈H) ∧ (∀ {a b:G}, (a∈H) → (b∈H) → ((a * b)∈H))


Statement (preamble :=
 have one_mem : 1 ∈ H := ?one_mem
 have inv_mem : ∀ {a:G}, a∈H → a⁻¹∈H := ?inv_mem
 have mul_mem : ∀ {a b:G}, (a∈H) → (b∈H) → ((a * b)∈H) := ?mul_mem
 exact ⟨h1, inv_mem, mul_mem⟩
 pick_goal 2
 pick_goal 3
) (h1 : H.Nonempty) (h2 :∀ {a b:G}, (a∈H) → (b∈H) → ((a * b⁻¹)∈H)) : IsSubgroup H := by
  Hint "We claim that the identity `1` is in `H`.
  Use `have one_mem : 1 ∈ H := ?_' to introduce this claim."
  Hint "Now we use the claim to finish the proof.
  Use `split_ands' to split the goal into three parts."
  · Hint "First take an arbitrary element x in H. Use `obtain ⟨x, hx⟩ := h1` to obtain this fact."
    obtain ⟨x, hx⟩ := h1
    Hint "Use `specialize' to replace `{h2}' with `{h2} {hx} {hx}' "
    Hint (hidden := true) "Use `specialize {h2} {hx} {hx}'."
    specialize h2 hx hx
    Hint "Use `mul_inv_cancel` to clear up {h2}"
    Hint (hidden := true) "Use `rw [mul_inv_cancel] at {h2}'."
    rw [mul_inv_cancel] at h2
    Hint "Now we can use `assumption' to finish the goal."
    assumption
  · Hint "Take an arbitrary element a in {H}. Use `intro a ha' to introduce this fact."
    intro a ha
    Hint "Prove `a⁻¹∈ H' using `h2' "
    Hint (hidden := true) "Use `specialize {h2} {one_mem} {ha}'."
    specialize h2 one_mem ha
    Hint "Now use `one_mul` to clear up {h2}"
    rw [one_mul] at h2
    Hint "Except using `exact {h2}' one also can use `assumption' to finish the goal.  "
    assumption
  · Hint "Intro all the hypothesis by `intro a b ha hb'  "
    intro a b ha hb
    Hint "Show that b⁻¹ ∈ H by specialize `{inv_mem}' with `{inv_mem} {hb}'"
    specialize inv_mem hb
    Hint "Use {inv_mem} and {h2}"
    Hint (hidden := true) "Use `specialize {h2} {ha} {inv_mem}'."
    specialize h2 ha inv_mem
    Hint "Observe that `b⁻¹ ⁻¹ = b`."
    Hint (hidden := true) "Use `rw [inv_inv] at {h2}'."
    rw [inv_inv] at h2
    Hint "Now we can use `assumption' to finish the goal."
    assumption




NewTheorem inv_inv mul_one one_mul mul_inv_cancel inv_mul_cancel
