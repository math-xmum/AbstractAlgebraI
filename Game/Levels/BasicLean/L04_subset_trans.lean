import Game.Metadata

World "BasicLean"
Level 4

Title "Containing relation is transitive."


Introduction "The following statement claims that if set $r$ is a subset of set $s$, and set $s$ is a subset of set $t$, then set $r$ is a subset of set $t$. This is a transitive property of subsets, showing that if a set is a subset of another, and that second set is a subset of a third, then the first set is a subset of the third."

Statement subset_trans' {α : Type*} (r s t : Set α): r ⊆ s → s ⊆ t → r ⊆ t := by
  Hint "We start by introducing the hypotheses h₁ that $r ⊆ s$, h₂ that $s \\subseteq t$, and an arbitrary element x with hx that x is an element of $r$. You can use `intro`."
  intro h₁ h₂ x hx
  Hint "To show that {x} is an element of $t$, we can apply the subset property {h₂}, which requires showing that {x} is an element of $s$. You can use `apply {h₂}`."
  apply h₂
  Hint "Now, we need to show that {x} is an element of $s$. We can use the subset property {h₁}, which requires showing that {x} is an element of $r$. You can use `apply {h₁}`."
  apply h₁
  Hint "At this point, we need to show {x} is an element of $r$, which we know from our hypothesis {hx}. You can use `exact {hx}`."
  exact hx


Conclusion "Level Completed!"

NewTactic intro exact apply
