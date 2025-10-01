import Game.Metadata

World "Equivalence"

Level 4



variable (n: ℕ)


Statement : Equivalence (α := ℕ) (fun a b => a % n = b % n) := by
  constructor
  Hint "We already use `constructor` to split the goal into three parts."
  Hint "Use `intro` to introduce the variables."
  intro x
  Hint "This is obvious. Use `rfl` to close the goal."
  rfl
  Hint "Use `intro` to introduce the variables and the hypothesis."
  intro x y hxy
  Hint "Use `rw` to rewrite the goal using the hypothesis {hxy}."
  rw [hxy]
  Hint "Use `intro` to introduce the variables and the hypothesis."
  intro x y z hxy hyz
  Hint "Use `rw` to rewrite the goal using the hypothesis {hxy} and {hyz}."
  rw [hxy, hyz]
