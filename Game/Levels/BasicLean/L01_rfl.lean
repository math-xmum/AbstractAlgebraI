import Game.Metadata
--import Game.Generator.Basic

World "BasicLean"
Level 1

Title "Rfl tactic"

Introduction "This level gets you familiar with the game interface."

Introduction "This statement claims that $2 + 2 = 4$, which is a basic arithmetic equality that holds by definition in Lean's natural number system. The proof can be established through simple computation."
Statement : 2 + 2 = 4 := by
  Hint (hidden := true) "The equality can be settled by evaluation. You can use either `rfl` or power-tactics such as `trivial`, `norm_num` and `simp`."
  Branch
    rfl
  Branch
    simp
  Branch
    trivial
  norm_num


Conclusion "rfl and norm_num are very handy to close obvious goals."

/- Use these commands to add items to the game's inventory. -/

NewTactic rfl norm_num simp trivial

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
