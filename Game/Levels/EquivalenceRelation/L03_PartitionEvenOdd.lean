import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "Equivalence Relation"

Level 1

def IsPartition (c : Set (Set α)) := ∅ ∉ c ∧ ∀ a, ∃! b, b ∈ c ∧ a ∈ b


#check Odd

Statement : IsPartition {{x : ℕ | Even x}, {x : ℕ | Odd x}} := by
  unfold IsPartition
  constructor
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  push_neg
  constructor
  use 0; decide
  use 1; decide
  intro a
  by_cases h : Even a
  use {x : ℕ | Even x}
  simp
  constructor
  exact h
  intro ha
  exfalso
  exact ha h
  use {x : ℕ | Odd x}
  simp
  constructor
  exact h
  intro h'
  exfalso
  exact h h'




  --suffices {x:ℕ  | Even x} ∪ {x:ℕ | ¬ Even x} = Set.univ from by simp
  --rw [Set.sUnion_insert, Set.sUnion_singleton]





NewTactic «intro» rfl rw exact simp «have» by_cases simp exfalso by_cases
OnlyTactic intro rfl rw exact simp «have» by_cases simp exfalso by_cases
