import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 3

Introduction "
A semi-group is a set $G$ with a binary operation $*$ such that $*$ has associative law.
"

variable (G :Type*) [Semigroup G]

Statement (a b c : G) : (a * b) * c = a * (b * c)  := by
  Hint "Use `group`"
  group

NewTactic rw rfl apply group
