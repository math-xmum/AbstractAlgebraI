import Game.Metadata

World "BasicFunctions"
Level 6
Title "Composition of surjective function."

Introduction "The following statement claims that the composition of two bijective functions is also bijective. Specifically, if $f: α → β$ and $g: β → γ$ are both bijective, then $g ∘ f: α → γ$ is also bijective. A bijective function is both injective (one-to-one) and surjective (onto)."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (g ∘ f) := by
  Hint "To prove that $g ∘ f$ is bijective, we need to show it is both injective and surjective. You can use `constructor` to split the goal into these two parts."
  constructor
  Hint "First, we prove injectivity of $g ∘ f$. We need to show that if $(g ∘ f)(x) = (g ∘ f)(y)$, then $x = y$. You can use `intro` to introduce variables x and y and hypothesis h."
  intro x y h
  Hint "To show $x = y$, we can use the injectivity of {f} (since $f$ is bijective). You can use `apply {hf}.1` to reduce the goal to showing $f(x) = f(y)$."
  apply hf.1
  Hint "Now, to show $f(x) = f(y)$, we can use the injectivity of {g} (since $g$ is bijective). You can use `apply {hg}.1` to reduce the goal to showing $g(f(x)) = g(f(y))$."
  apply hg.1
  Hint "The goal $g(f(x)) = g(f(y))$ is exactly our hypothesis {h}, so we can use `exact {h}`."
  exact h
  Hint "Now, we prove surjectivity of $g ∘ f$. We need to show that for any $y : γ$, there exists an $a : α$ such that $(g ∘ f)(a) = y$. You can use `intro` to introduce y."
  intro y
  Hint "Since {g} is surjective, there exists some $x : β$ such that $g(x) = y$. You can use `rcases {hg}.2 {y} with ⟨x, hx⟩` to obtain such an x and the equality hx."
  rcases hg.2 y with ⟨x, hx⟩
  Hint "Since {f} is surjective, there exists some $a : α$ such that $f(a) = x$. You can use `rcases {hf}.2 {x} with ⟨a, ha⟩` to obtain such an a and the equality ha."
  rcases hf.2 x with ⟨a, ha⟩
  Hint "We can now use {a} as our witness for the existential. You can use `use {a}` to set up the goal $(g ∘ f)(a) = y$."
  use a
  Hint "To prove $(g ∘ f)(a) = y$, we can rewrite using {hx} and {ha}. You can use `rw [← {hx}, ← {ha}]` to simplify the goal."
  rw [← hx, ← ha]
  Hint "The goal now reduces to $(g ∘ f)(a) = g(f(a))$, which is true by definition of function composition. You can use `rfl` to finish the proof."
  rfl


Conclusion "Level Completed!"
NewTactic intro apply exact use rw rfl
