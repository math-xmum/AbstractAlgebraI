import Game.Metadata

World "BasicFunctions"
Level 6
Title "Composition of surjective function."

Introduction "The following statement claims that the composition of two bijective functions is also bijective. Specifically, if $f: α → β$ and $g: β → γ$ are both bijective, then $g ∘ f: α → γ$ is also bijective. A bijective function is both injective (one-to-one) and surjective (onto)."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (g ∘ f) := by
  Hint "To prove that $g ∘ f$ is bijective, we need to show it is both injective and surjective. You can use `unfold Function.Bijective at *` to unfold the definition of bijective function."
  unfold Function.Bijective at *
  Hint "Now use `constructor` to split the goal into these two parts."
  constructor
  Hint "Now use `Function.Injective.comp` to prove the injectivity of $g ∘ f$. You can use `Function.Injective.comp {hg}.1 {hf}.1` to prove the injectivity of $g ∘ f$."
  exact Function.Injective.comp hg.1 hf.1
  Hint "Now use `Function.Surjective.comp` to prove the surjectivity of $g ∘ f$. You can use `Function.Surjective.comp {hg}.2 {hf}.2` to prove the surjectivity of $g ∘ f$."
  exact Function.Surjective.comp hg.2 hf.2


Conclusion "Level Completed! We unlock the following theorem: Function.Bijective.comp"

NewTactic constructor intro apply exact use rw rfl
NewTheorem Function.Bijective.comp
