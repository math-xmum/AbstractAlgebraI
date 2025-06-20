import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]


abbrev Setoid.equivclass (x : α):  Set α := {y | x ≈ y}

Statement Setoid.equivclass_nonempty (x : α) : Setoid.equivclass x ≠ ∅ := by
   push_neg
   use x
   unfold Setoid.equivclass
   rewrite [Set.mem_setOf_eq]
   rfl

NewTheorem Setoid.equivclass_nonempty
NewDefinition Setoid.equivclass
NewTactic rewrite
OnlyTactic rewrite push_neg use unfold rfl
