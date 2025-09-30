import Game.Metadata


World "Partition"

Level 4


variable (n : ℕ) [NeZero n]

Statement (preamble :=
  have h1 :  ∀ y : Fin n, {x : ℕ | x % n = y } = (Fin.ofNat n) ⁻¹' {y} := by
    intro y
    unfold Fin.ofNat
    ext x
    rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    apply Iff.intro
    · intro a
      simp_all only [Fin.eta]
    · intro a
      subst a
      simp_all only
  have h2 : Function.Surjective $ Fin.ofNat n := ?_
): Setoid.IsPartition $ Set.range (fun (y : Fin n) ↦ {x : ℕ | x % n = y}) := by
  Hint "Fin.ofNat n : ℕ → Fin n is the map send a natural number to its residue r modulo n (0 ≤ r < n).
  We start by rewriting the goal using the lemma `h1`."
  simp_rw [h1]
  Hint "We now apply the lemma `Function.fiber_of_surjective_partition`."
  exact Function.fiber_of_surjective_partition h2
  · Hint "We now need to prove that `Fin.ofNat n` is surjective."
    intro x
    Hint "We now use `use` to construct a witness for the existential."
    use x.val
    Hint "We use `simp` to close the goal."
    simp

NewTactic simp_rw simp
NewTheorem Function.fiber_of_surjective_partition
