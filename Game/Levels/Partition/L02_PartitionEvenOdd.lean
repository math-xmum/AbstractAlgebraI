import Game.Metadata

World "Partition"

Level 2

variable {α : Type*} (C : Set (Set α))



Statement :
  let Seven := {x : ℕ | Even x}
  let Sodd := {x : ℕ  | Odd x}
  let C := {Seven, Sodd}
  Setoid.IsPartition C := by
  constructor
  · rw [Set.mem_pair_iff]
    push_neg
    constructor
    use 0; decide
    use 1; decide
  · intro a
    by_cases h : Even a
    use Seven
    simp
    constructor
    · rw [Set.mem_pair_iff]
      constructor
      · left
        rfl
      · exact h
    · intro S hS ha
      rw [Set.mem_pair_iff] at hS
      rcases hS with H | H
      exact H
      rw [H] at ha
      exfalso
      rw [<-Nat.not_odd_iff_even] at h
      exact h ha
    · rw [Nat.not_even_iff_odd] at h
      use Sodd
      simp
      rw [Set.mem_pair_iff]
      simp
      constructor
      exact h
      intro S hS ha
      rcases hS with H | H
      · rw [H] at ha
        exfalso
        rw [<-Nat.not_even_iff_odd] at h
        exact h ha
      · exact H

OnlyTactic rfl
NewTheorem Set.mem_pair_iff
