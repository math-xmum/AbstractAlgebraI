import Game.Metadata

World "Partition"

Level 2

variable {α : Type*} (C : Set (Set α))

Introduction "We will prove that the set of even and odd numbers is a partition of the natural numbers.

More precisely, let Seven := {x : ℕ | Even x} and Sodd := {x : ℕ | Odd x}.
We will prove that C := {Seven, Sodd} is a partition of the natural numbers.

One need a lemma called `Set.mem_pair_iff` to translate the statement that c ∈ {a,b}
if and only if c = a or c = b.
"



Statement :
  let Seven := {x : ℕ | Even x}
  let Sodd := {x : ℕ  | Odd x}
  let C := {Seven, Sodd}
  Setoid.IsPartition C := by
  Hint "We start by unfolding the definition of a partition. Use `unfold Setoid.IsPartition`."
  unfold Setoid.IsPartition
  Hint "Now we need to prove that the collection is not empty and that each element belongs to exactly one of \{{Seven}, {Sodd}}. Use `constructor`."
  constructor
  · Hint "Use `rw [Set.mem_pair_iff]` to translate the statement that ∅ ∈  C if and only if ∅ = {Seven} or ∅ = {Sodd}."
    rw [Set.mem_pair_iff]
    Hint "
    There is few ways to prove the goal. `push_neg` is one of the way to simplify the statement having negations.
    Use `push_neg` to push the negation inside the statement."
    push_neg
    Hint "Use `constructor` to split the goal."
    constructor
    Hint "To show a set is Nonempty is to provide an element of the set. Use `use 0` and reduce the goal to show that 0 ∈ {Seven}."
    use 0
    Hint "This is decidable by Lean and is trivial. Use `decide` or `trivial`. "
    decide
    Hint "One can combine two commands in one line using `;`. Try `use 1; decide`."
    use 1; decide
  · Hint "We need to prove that each element belongs to exactly one of \{{Seven}, {Sodd}}. Use `intro a`."
    intro a
    Hint "Use `by_cases` to split the goal into two cases: `Even a` and `¬ Even a`."
    by_cases h : Even a
    Hint "Use `use Seven` to show that `a` belongs to `Seven`."
    use Seven
    Hint "Use `simp` to make the goal more readable."
    simp
    Hint "Use `constructor` to split the goal."
    constructor
    · Hint "Use `rw [Set.mem_pair_iff]` to translate the statement that `Seven` belongs to `C` if and only if `Seven` = `Seven` or `Seven` = `Sodd`."
      rw [Set.mem_pair_iff]
      Hint "Use `constructor` to split the goal."
      constructor
      · Hint (hidden := true) "Use `left` to show that `Seven` = `Seven`."
        left
        Hint (hidden := true) "Use `rfl` to show that `Seven` = `Seven`."
        rfl
      · Hint (hidden := true) "Use `exact h` to show that `{a} ∈  {Seven}`."
        exact h
    · Hint "Use `intro S hS ha` to introduce the hypothesis."
      intro S hS ha
      Hint "Use `rw [Set.mem_pair_iff]` to translate the statement that `S` belongs to `C` if and only if `S` = `Seven` or `S` = `Sodd`."
      rw [Set.mem_pair_iff] at hS
      Hint "Use `rcases {hS} with H | H` to split the goal into two cases: `H` and `H`."
      rcases hS with H | H
      Hint "This is exactly {H}."
      exact H
      Hint "Use `rw [{H}] at {ha}` to rewrite {ha}."
      rw [H] at ha
      Hint "Use `exfalso` to indicate that our the goal is show that the assumptions are contradictory."
      exfalso
      Hint "Use `rw [<-Nat.not_odd_iff_even] at h` to rewrite {h}."
      rw [<-Nat.not_odd_iff_even] at h
      Hint "Use `exact h ha` to show that the goal is false. One also can use `contradiction`."
      exact h ha
    · Hint "The proof is similar to the previous case. "
      Hint (hidden := true) "Use `rw [Nat.not_even_iff_odd] at h` to rewrite {h}."
      rw [Nat.not_even_iff_odd] at h
      Hint (hidden := true) "Use `use Sodd` to show that `a` belongs to `Sodd`."
      use Sodd
      Hint (hidden := true) "Use `simp` to make the goal more readable."
      simp
      Hint (hidden := true) "Use `rw [Set.mem_pair_iff]` to translate the statement that `S` belongs to `C` if and only if `S` = `Seven` or `S` = `Sodd`."
      rw [Set.mem_pair_iff]
      Hint (hidden := true) "Use `simp` to make the goal more readable."
      simp
      Hint (hidden := true) "Use `constructor` to split the goal."
      constructor
      Hint (hidden := true) "Use `exact h` to show that `{a} ∈ {Sodd}`."
      exact h
      Hint (hidden := true) "Use `intro S hS ha` to introduce the hypothesis."
      intro S hS ha
      Hint (hidden := true) "Use `rcases {hS} with H | H` to split the goal into two cases: `H` and `H`."
      rcases hS with H | H
      · Hint (hidden := true) "Use `rw [H] at ha` to rewrite {ha}."
        rw [H] at ha
        Hint (hidden := true) "Use `exfalso` to indicate that our the goal is show that the assumptions are contradictory."
        exfalso
        Hint (hidden := true) "Use `rw [<-Nat.not_even_iff_odd] at h` to rewrite {h}."
        rw [<-Nat.not_even_iff_odd] at h
        Hint "Use `exact h ha` to show that the goal is false. One also can use `contradiction`."
        exact h ha
      · Hint (hidden := true) "Use `exact H` to close the goal."
        exact H

NewTactic exfalso trivial «have» simp trivial push_neg contradiction
NewTheorem Set.mem_pair_iff Nat.not_odd_iff_even Nat.not_even_iff_odd

#check (⟨ 0, 1 ⟩ : ℕ × ℕ )
