import Game.Metadata

World "BasicLean"
Level 8

Title "Intersection is commutative."

Introduction "The following statement claims that the intersection of sets $s$ and $t$ is equal to the intersection of sets $t$ and $s$. This is a statement about the commutativity of set intersection, showing that the order of sets in an intersection can be swapped."

Statement {α : Type*} (s t : Set α): s ∩ t = t ∩ s := by
  Hint "To prove set equality, we start by showing that for any element $x$, $x$ is in $s ∩ t$ if and only if $x$ is in $t ∩ s$. You can use `ext` to introduce this element $x$."
  ext x
  Hint "Rewrite the goal using the definition of set intersection. You can use `rw [Set.mem_inter_iff]`."
  rw [Set.mem_inter_iff]
  Hint "To prove the bi-implication, we need to prove both directions separately. You can use `constructor`."
  constructor
  Hint "For the forward direction (${x} ∈ s ∧ {x} ∈ t → {x} ∈ t ∩ s$), we can use the hypothesis that $x ∈ s$ and $x ∈ t$, and simply swap them to show ${x} ∈ t$ and ${x} ∈ s$. You can use `rintro ⟨xs, xt⟩` followed by `exact ⟨xt, xs⟩`."
  · rintro ⟨xs, xt⟩
    exact ⟨xt, xs⟩
  Hint "For the reverse direction (${x} ∈ t ∩ s → {x} ∈ s ∧ {x} ∈ t$), similarly, we use the hypothesis that ${x} ∈ t$ and ${x} ∈ s$, and swap them to show ${x} ∈ s$ and ${x} ∈ t$. You can use `rintro ⟨xt, xs⟩` followed by `exact ⟨xs, xt⟩`."
  · rintro ⟨xt, xs⟩
    exact ⟨xs, xt⟩



Conclusion "Level Completed! We unlock the theorem: Set.inter_comm"
NewTactic ext rintro constructor
NewTheorem Set.inter_comm
