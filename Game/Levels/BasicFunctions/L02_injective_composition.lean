import Game.Metadata

World "BasicFunctions"
Level 2
Title "Composition of injective function."

Introduction "The following statement claims that the composition of two injective functions is also injective. Specifically, if $f: α → β$ and $g: β → γ$ are both injective functions, then the composition $g ∘  f: α →  γ$ is also injective."
Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Injective f) (hg : Function.Injective g) : Function.Injective (g ∘ f) := by
  Hint " We start by introducing the variables x, y and the hypothesis h that (g ∘ f) x = (g ∘ f) y. You can use `intro`. "
  intro x y h
  Hint "To show {x} = {y}, we first need to show that f {x} = f {y}. We can use the injectivity of {f}, given by {hf}. You can use `apply {hf}`. "
  apply hf
  Hint "We need to show g (f {x}) = g (f {y}), which follows from the hypothesis {h}. You can use `apply {hg}`. "
  apply hg
  Hint "The hypothesis {h} directly gives us g (f {x}) = g (f {y}). You can use `exact {h}`. "
  exact h


NewTactic apply intro exact rw
Conclusion "Level Completed!"
