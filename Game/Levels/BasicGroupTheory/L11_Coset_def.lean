import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 11

Introduction "
Let H be a subgroup of G.
The subset g • H := {gh | h∈H} for some g∈G is called a left coset of H.

Basically all cosets are essentially the same in the sense that there is a natural bijection between g H and k H for arbitrary g k ∈ G.

In Lean, a bijection between two types α and β is represented by the type `Equiv α β'
"

open Monoid Group
open scoped Pointwise

variable {G : Type*} [Group G] {g k:G} {H : Set G}


Statement :
  Equiv (g • H :Set G) (k • H : Set G):= by
  Hint "Use `constructor' to expend the definition of Equiv"
  constructor
  Hint "Pick the 3rd goal, which required to define a map from g • H to k • H using `pick_goal 3'"
  pick_goal 3
  · Hint " Define the map g • H ∋ x ↦ (k * g⁻¹)*x. On can achive this by using `use fun x => ⟨(k * g⁻¹)*x, ?_⟩'
    Here we need to prove that the function is well defined, i.e.  `(k * g⁻¹)*x ∈ k • H'
    "
    use fun x => ⟨(k * g⁻¹)*x, ?_⟩
    Hint " x ∈ g • H means ∃ h ∈ H, g • h = x  "
    obtain ⟨h,b,hh⟩ := x.2
    Hint "One can clear up the expression in {hh} by `simp at {hh}'"
    simp at hh
    Hint "To show k * g⁻¹ * ↑x ∈ k • H, one should provide an element a in h such that k g⁻¹ x  = k a. Ore one can try to replace x by g*h first and simplify the expression using `group'."
    rw [<-hh]
    group
    Hint "Now `use h'. "
    use h
    trivial
  Hint "Now construct the inverse function by  `pick_goal 3'"
  pick_goal 3
  · Hint "This is the same as the first case. We let you to practice by yourself."
    use fun x => ⟨(g * k⁻¹)*x, ?_⟩
    obtain ⟨h,b,hh⟩ := x.2
    simp at hh
    rw [<-hh]
    group
    Hint "Now `use h'. "
    use h
    trivial
  · Hint "`Function.LeftInverse g f' means ∀ x, g (f x) = x. So we use `intro' to reveal the goal. "
    intro x
    Hint "Since `x' is a subtype, `y = x' if and only if the `y.1 = x.1'. Use `ext' to reduced the problem to comparing the values hold in  y and x. "
    ext
    Hint "Use `simp' to clear up the goal"
    simp
    Hint "Use `group' to finish the proof. "
    group
  · Hint "This is similar to the pervious case."
    intro x
    ext;group


NewTheorem Set
