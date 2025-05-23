import Game.Metadata

World "BasicFunctions"
Level 1
Title "Definition of injective function."

Introduction "The statement we are about to prove is a characterization of the injectivity of a function. It states that a function $f$ from $\\alpha$ to $\\beta$ is injective if and only if for every pair of elements $x$ and $y$ in $\\alpha$, $f(x) = f(y)$ implies $x = y$. This is a fundamental property of injective functions, which ensures that different inputs map to different outputs."
Statement {α β γ : Type} (f : α → β) (g : β → γ) : Function.Injective f ↔ ∀ x y, f x = f y → x = y := by 
  Hint "The goal is already in the form of a well-known equivalence for injective functions. Therefore, we can conclude the proof directly using `rfl`, which shows that both sides of the equivalence are equal by definition."
  rfl


Conclusion "Level Completed!"

NewTactic «suffices» obtain
