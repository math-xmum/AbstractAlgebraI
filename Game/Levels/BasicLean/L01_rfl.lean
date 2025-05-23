import Game.Metadata

World "BasicLean"
Level 1

Title "Rfl tactic"

Introduction "This level gets you familiar with the game interface."

Statement : 2 + 2 = 4 := by
  Hint "The equality can be settaled by evaluation."
  Hint "You can use either `rfl` or `norm_num`."
  Branch
    rfl
  norm_num


Conclusion "rfl and norm_num are very handy to close obvious goals."

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl norm_num apply intro exact rcases

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
