import Game.Metadata
import Reap

World "Equivalence Relation"

Level 1


variable {α β : Type*}

Introduction "The following statement claims that the graph of a function `f : α →  β`, a relation that satisfies the property that for each element a in α, there exists a unique element b in β such that (a,b) ∈ Function.graph f."

Statement (f : α → β) :
  ∀ a, ∃! b, (a,b) ∈ Function.graph f := by
  Hint "Use `unfold` to unfold the definition of `Function.graph`."
  unfold Function.graph
  Hint "Now use `intro` to introduce the element a in α. "
  intro a
  Hint "Use `use` to exist a element b in β such that (a,b) ∈ Function.graph f."
  use f a
  Hint "Use `beta_reduce` to reduce the goal."
  beta_reduce
  Hint (hidden := true) "Use `constructor` to split the goal."
  constructor
  · Hint (hidden := true) "Use `rfl` to close the first goal."
    rfl
  · Hint (hidden := true) "Use `intro` to introduce the element y in β and the hypothesis H. "
    intro y H
    Hint (hidden := true) "Use `rw` to rewrite the goal using the hypothesis H."
    rw [H]

Conclusion "Level Completed! We unlock the theorem: SetRel.exists_graph_eq_iff."

NewTheorem SetRel.exists_graph_eq_iff
