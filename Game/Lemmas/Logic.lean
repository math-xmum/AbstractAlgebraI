import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Setoid.Partition


/--
For any type `α` and elements `a`, `b`, and `c`, the membership of `c` in the set `{a, b}` is equivalent to `c` being equal to `a` or `b`.
-/
@[simp]
lemma Set.mem_pair_iff {α :Type*} {a b c : α} :  c ∈ ({a, b} : Set α ) ↔ c = a ∨ c = b := by
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]

lemma Function.fiber_of_surjective_partition {α β : Type*} {f : α → β} (h : Function.Surjective f) : Setoid.IsPartition $ Set.range (fun (y : β) ↦ f ⁻¹' {y}) := by
   sorry
