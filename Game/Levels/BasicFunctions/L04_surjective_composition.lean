import Game.Metadata

World "BasicFunctions"
Level 4
Title "Composition of surjective function."


Introduction "The following statement shows that the composition of two surjective functions is also surjective. That is, if $f: α → β$ and $g: β → γ$ are both surjective, then $g ∘ f: α → γ$ is surjective."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (g ∘ f) := by
  Hint "To prove that $g ∘ f$ is surjective, we need to show that for every $y$ in $γ$, there exists some $a$ in $α$ such that $(g ∘ f)(a) = y$. We start by introducing an arbitrary element y of $γ$."
  Hint "First unfold Function.Surjective"
  unfold Function.Surjective at *
  Hint "Next, we introduce an arbitrary element $c$ in $γ$."
  intro c
  Hint "Since $g$ is surjective, there exists some $b$ in $β$ such that $g(b) = c$. We can use `obtain` to obtain such a $b$ and the equality $hb$."
  obtain ⟨b,hb⟩ := hg c
  Hint "Since $f$ is surjective, there exists some $a$ in $α$ such that $f(a) = b$. We can use `obtain` to obtain such a $a$ and the equality $ha$."
  obtain ⟨a,ha⟩ := hf b
  Hint "We can now use $a$ as our witness for the existential. We can use `use {a}` to set up the goal $(g ∘ f)(a) = c$."
  use a
  Hint "We can now use $hb$ and $ha$ to rewrite the goal $(g ∘ f)(a) = c$."
  rw [<-hb]
  Hint "We can now use $ha$ to rewrite the goal $(g ∘ f)(a) = c$."
  rw [<-ha]
  Hint "The goal now reduces to $g(f(a)) = g(b)$ and $f(a) = b$, which is true by definition of function composition. We can use `rfl` to finish the proof."
  rfl




Conclusion "Level Completed! We unlock the following theorem: Function.Surjective.comp."
NewTactic use obtain intro rw
NewTheorem Function.Surjective.comp
