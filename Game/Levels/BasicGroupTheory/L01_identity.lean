import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 1

Introduction "
Suppose $G$ is a set with a binary operation $*$.

The following statement claims that identity element is unique.

Suppose $e$ and $e'$ are two identity elements, we need to prove $e=e'$.
"

variable (G :Type*) [Mul G]

Statement (e e' : G) (h1:∀ g :G,  e*g = g) (h2: ∀ g :G, g * e=g) (h3:∀ g :G,  e'*g = g) (h4: ∀ g :G, g * e'=g) : e=e'  := by
  Hint "Use `h1` "
  rw [<- h1 e']
  Hint "Use `h4` "
  rw [h4 e]


NewTactic rw rfl apply exact omega «have»  «let» «show» «calc»
NewTheorem have_intro
