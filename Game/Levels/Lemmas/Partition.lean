import Mathlib.Order.SetNotation
import Mathlib.Init.Logic
import Mathlib.Init.Set


/-- A collection `c : Set (Set α)` of sets is a partition of `α` into pairwise
disjoint sets if `∅ ∉ c` and each element `a : α` belongs to a unique set `b ∈ c`. -/
def IsPartition (c : Set (Set α)) := ∅ ∉ c ∧ ∀ a, ∃! b, b ∈ c ∧ a ∈ b

def IsPartition' (c : Set (Set α)) := ∅ ∉ c ∧ ( ⋃₀ c = Set.univ) ∧ ( ∀ a ∈ c,  ∀ b ∈ c, a ∩ b ≠ ∅ → a = b)

#print IsPartition'
