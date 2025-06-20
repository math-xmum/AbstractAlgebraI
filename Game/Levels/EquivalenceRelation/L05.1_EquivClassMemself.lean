import Game.Metadata
import Game.Generator.Basic
-- import Mathlib

World "EquivalenceRelation"

Level 1


variable {α :Type*} [inst: Setoid α]


Statement Setoid.mem_selfequivclass
(x : α) : x ∈ Setoid.equivclass x  := by
   rewrite [Set.mem_setOf_eq]
   exact Setoid.refl _


NewDefinition Setoid.equivclass
NewTactic rewrite
OnlyTactic rewrite push_neg use unfold rfl
