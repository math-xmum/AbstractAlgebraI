import Game.Metadata

World "BasicFunctions"
Level 3
Title "Definition of surjective function."

--#Genhint
Statement {α β γ : Type} (f : α → β) : Function.Surjective f ↔ ∀ y, ∃ x, f x = y := by
  Hint "Since the statement directly matches the definition of surjectivity, you can use `rfl` to complete the proof."
  rfl


Conclusion "Level Completed!"
