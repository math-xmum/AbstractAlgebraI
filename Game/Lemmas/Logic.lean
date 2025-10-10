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
   unfold Setoid.IsPartition
   constructor
   · intro he
     obtain ⟨y,he⟩ := he
     obtain ⟨x,hx⟩ := h y
     have hx: x ∈ f ⁻¹' {y} := hx
     beta_reduce at he
     rw [he] at hx
     contradiction
   · intro a
     use (f ⁻¹' {f a})
     beta_reduce
     constructor
     · simp only [Set.mem_range, exists_apply_eq_apply, Set.mem_preimage, Set.mem_singleton_iff,
       and_self]
     · intro y
       intro ⟨hy1,hy2⟩
       obtain ⟨z,hz1⟩ := hy1
       beta_reduce at hz1
       rw  [<-hz1] at hy2
       rw [<-hz1]
       have hz2 : f a = z := by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hy2
        exact hy2
       rw [hz2]
