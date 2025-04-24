import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 3

Introduction "
A  monoid is a semi-group with identity and .

A  group is a monoid such that every element has inverse.
"

variable (G :Type*) [Group G]

Statement (a: G) : ∃ (b:G), (a*b =1 ∧ b*a = 1)  := by
  Hint "Use `a⁻¹`"
  use a⁻¹
  --Hint "Use `constructor` to split the goal"
  Hint "Also can use And.intro to split the goal"
  apply And.intro
  · Hint "Use `group`"
    group
  · Hint "Use `group`"
    group


NewTactic use rw rfl apply group constructor
NewTheorem And.intro
