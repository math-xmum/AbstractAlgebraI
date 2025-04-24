import Game.Metadata

World "BasicFunctions"
Level 3
Title "Definition of surjective function."

Statement {α β γ : Type} (f : α → β) (g : β → γ) : Function.Surjective f ↔ ∀ y, ∃ x, f x = y := by
  rfl

Conclusion "Level Completed!"
