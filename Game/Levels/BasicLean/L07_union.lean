import Game.Metadata

World "BasicLean"
Level 7

Title "Definition of union."

Introduction "The statement is about set theory. It claims that for any element $x$, the membership of $x$ in the union of sets $s$ and $t$ is equivalent to $x$ being a member of either set $s$ or set $t$. This is a fundamental property of set unions."
Statement {α : Type*} (s t : Set α) (x : α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := by
  Hint "The goal is to prove an equivalence between two statements: $x ∈ s ∪ t$ and $x ∈ s ∨ x ∈ t$. We can achieve this by using the rewrite tactic with the known property of set unions. You can use `rw [Set.mem_union]` to transform the goal accordingly.
  Simply use `rfl` also works as it is the definition of union."
  rw [Set.mem_union]


Conclusion "Level Completed!"
NewTheorem Set.mem_union
