import Game.Metadata

World "BasicFunctions"
Level 2
Title "Composition of injective function."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (g ∘ f) := by
  intro x y  h
  apply hf
  apply hg
  exact h

NewTactic apply intro exact rw
Conclusion "Level Completed!"
