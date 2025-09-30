import Game.Metadata

World "BasicLean"
Level 5

Title "Containing relation is reflexive."

Introduction "The following statement asserts that for a set $s$ of type $\\alpha$, $s$ is a subset of itself. This is a fundamental property of sets, known as reflexivity of subset relation."
Statement  {α : Type*} (s : Set α) : s ⊆ s := by
  Hint "We start by introducing an arbitrary element x of the set s and a hypothesis xs stating that x is a member of {s}. You can use `intro`."
  intro x xs
  Hint "The goal is to show that {x} is in {s}, which is already given by the hypothesis {xs}. You can use `exact {xs}`."
  exact xs

Conclusion "Level Completed! We unlock the following theorem: subset_rfl"
NewTheorem subset_rfl
