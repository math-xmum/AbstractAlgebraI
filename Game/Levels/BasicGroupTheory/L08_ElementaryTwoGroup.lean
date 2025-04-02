import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 8

Introduction "
If $G$ is a group such that $a * a = 1$ for all $a in G$, then $G$ is abelian.
"

open Monoid Group

variable {G : Type*} [Group G]

/-
If $G$ is a group such that $a^2 = 1$ for all $a in G$, then $G$ is abelian.
"
-/

Statement  (H: ∀ a : G, a * a = 1) : ∀ a b :G, a*b=b*a := by
  have inv_eq_self : ∀ a : G, a⁻¹ = a := by
    intro a
    Hint "Use `mul_right_cancel' to translate the goal"
    apply mul_right_cancel (b:=a)
    Hint "Use the hypothesis"
    rw [H]
    Hint "Use `group' to finish the proof"
    group
  intro a b
  Hint "Use {inv_eq_self} smartly"
  Hint "You can use `nth_rw' to specify the location of the term to rewrite"
  rw [<-inv_eq_self (a * b)]
  nth_rw 1 [<-inv_eq_self a]
  nth_rw 1 [<-inv_eq_self b]
  Hint "Use `group' to finish the proof"
  group


NewTactic nth_rw
