import Game.Metadata

World "BasicLean"
Level 2

Title "Rewrite"

Introduction "This level gets you familiar with the game interface."


Statement (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can use rw [h] to rewrite `x` by `2`."
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "rw is the most basic command you can use."

/- Use these commands to add items to the game's inventory. -/
--TacticDoc rw --"rewrite the goal or assumption"
NewTactic rw
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
