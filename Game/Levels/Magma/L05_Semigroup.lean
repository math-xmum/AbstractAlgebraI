import Game.Metadata
-- import Mathlib

World "Magma"

Level 5

Introduction "
Recall that a magma is a set `G` with a binary operation `*` such that `a * b` is well-defined for all `a, b` in  `G`.

In this level, we will introduce the concept of a Semi-Group.
A Semi-Group is a magma `G`  such that `*` satisfies the associative law : (a * b) * c = a * (b * c).
"

variable (G :Type*) [Semigroup G]


Statement (a b c : G) : (a * b) * c = a * (b * c)  := by
  Hint "This is exactly the definition of semigroup.
  In Mathlib, one can use `mul_assoc` to prove the associativity of multiplication for any algebraic structure satisfying the associative law.
  Use `rw [mul_assoc]`
  or `rw [Semigroup.mul_assoc]`
  "
  Branch
    rw [mul_assoc]
  rw [Semigroup.mul_assoc]

Conclusion "We unlock the associativity of multiplication. You can use `mul_assoc` and `Semigroup.mul_assoc` to prove associativity of multiplication."
NewTheorem mul_assoc Semigroup.mul_assoc
