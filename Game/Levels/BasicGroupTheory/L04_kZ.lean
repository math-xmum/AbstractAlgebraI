import Game.Metadata
import Game.Levels.Lemmas.Group
-- import Mathlib

World "BasicGroupTheory"

Level 4

Introduction "
For example, ℤ is a group under addition.
Now the set of even integers, 2ℤ := {2n | n ∈ ℤ }, is a subgroup of ℤ.
More generally, kℤ := {k*n | n ∈ ℤ } is also a subgroup of ℤ.
Morover, all subgoup of ℤ is of the form kℤ for some k ∈ ℕ.

In fact, ℕ → {subgroup of ℤ} given by k ↦ kℤ is a bijection.
"



Statement (preamble :=
    apply Group.addsubgroup_make (· % k = 0)
) {k : ℤ} : AddSubgroup ℤ :=
  by
    Hint "This is clear. Use `simp` to simplify the goal."
    · simp
    Hint "Introduce elements a b and assumptions on them."
    Hint (hidden := true) "Use `intro a b ha hb` to introduce elements a b and assumptions."
    intro a b ha hb
    Hint "Use Int.sub_emod"
    Hint (hidden := true) "Use `rw [Int.sub_emod]` to rewrite the goal"
    rw [Int.sub_emod]
    Hint "Use hypothesis {ha} and {hb} to simp the goal"
    Hint (hidden := true) "Use `simp [ha,hb]` to simplify the goal"
    simp [ha,hb]


NewTheorem  Int.sub_emod Int.add_emod Group.addsubgroup_make
