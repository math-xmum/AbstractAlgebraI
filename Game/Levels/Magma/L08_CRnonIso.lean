
import Game.Metadata
import Game.Levels.Lemmas.Group

World "Magma"

Level 1

#check IsEmpty.mk
#check pow_two

Statement : IsEmpty (ℂ ≃* ℝ) :=  by
  apply IsEmpty.mk
  intro f
  let x := f.symm (-1)
  have hx : f x = -1 := MulEquiv.apply_symm_apply _ _
  have H := Complex.cpow_nat_inv_pow x (by decide : 2 ≠ 0)
  norm_cast at H
  rw [pow_two] at H
  apply_fun f at H
  rw [MulEquiv.map_mul] at H
  rw [hx] at H
  have H2 := sq_nonneg (f (x ^ (2:ℂ)⁻¹))
  rw [pow_two,H] at H2
  norm_num at H2

NewTheorem sq_nonneg Complex.cpow_nat_inv_pow pow_two
OnlyTactic «let» «have» rw norm_cast norm_num
