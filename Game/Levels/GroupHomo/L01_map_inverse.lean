import Game.Metadata
-- import Mathlib

World "GroupHomomorphism"

Level 1

Introduction "
Another easy consequence of the definition of group homomorphism,  f : H →* G, is that it sends inverse to inverse, i.e ∀ h : H f (h⁻¹) = (f h)⁻¹.
"
variable {G H:Type*} [Group G] [Group H]

Statement (f : H →* G) : ∀ h : H,  f h⁻¹ = (f h)⁻¹  := by


NewTheorem mul_left_cancel map_mul mul_one
NewTactic apply_fun
