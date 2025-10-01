import Game.Metadata

World "Equivalence"

Level 1

Introduction "The equivalence relation on a type α is a relation that is reflexive, symmetric, and transitive.
The following statement helps you to familiarize with the definition of equivalence relation in Mathlib.
"


variable {α :Type*} (r : α → α → Prop)



Statement (preamble := refine And.intro ?reflexive (And.intro ?symmetric ?transitive)) (H : Equivalence r) :  (∀ x, r x x) ∧ (∀ {x y}, r x y → r y x) ∧ (∀ {x y z}, r x y → r y z → r x z) := by
  Hint "Use `exact {H}.refl` to prove the goal."
  exact H.refl
  Hint "Use `exact {H}.symm` to prove the goal."
  exact H.symm
  Hint "Use `exact {H}.trans` to prove the goal."
  exact H.trans

NewDefinition Equivalence
