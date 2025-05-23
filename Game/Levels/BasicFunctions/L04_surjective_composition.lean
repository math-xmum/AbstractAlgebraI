import Game.Metadata

World "BasicFunctions"
Level 4
Title "Composition of surjective function."


Introduction "The following statement shows that the composition of two surjective functions is also surjective. That is, if $f: α → β$ and $g: β → γ$ are both surjective, then $g ∘ f: α → γ$ is surjective."

Statement {α β γ : Type} (f : α → β) (g : β → γ) (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (g ∘ f) := by
  Hint "To prove that $g ∘ f$ is surjective, we need to show that for every $y$ in $γ$, there exists some $a$ in $α$ such that $(g ∘ f)(a) = y$. We start by introducing an arbitrary element y of $γ$."
  intro y
  Hint "Since {g} is surjective (by {hg}), there exists some x in $β$ such that $g(x) = y$. We can use `rcases` with {hg} {y} to obtain this witness."
  rcases hg y with ⟨x, hx⟩
  Hint "Similarly, since {f} is surjective (by {hf}), there exists some a in $α$ such that $f(a) = x$. Again, we use `rcases` with {hf} {x} to obtain this witness."
  rcases hf x with ⟨a, ha⟩
  Hint "We now claim that this {a} is the element we're looking for. We use `use` to specify {a} as our candidate."
  use a
  Hint "We need to show $(g ∘ f)(a) = y$. Using our hypotheses {hx} ($g(x) = y$) and {ha} ($f(a) = x$), we can rewrite the goal. We use `rw` with these equalities."
  rw [← hx, ← ha]
  Hint "After rewriting, we're left with $(g ∘ f)(a) = g(f(a))$, which is true by definition of function composition. The `rfl` tactic finishes the proof."
  rfl

Conclusion "Level Completed!"
NewTactic use rcases intro rw
