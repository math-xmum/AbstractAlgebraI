import Game.Metadata
-- import Mathlib

World "BasicGroupTheory"

Level 6

Introduction "
Note that if inverse exits, then it is unique.
"
open Monoid
variable (G :Type*) [Monoid G]

Statement (a b c: G)
  (leftinvb : a * b = 1)
  (rightinvb : b * a = 1)
  (leftinvc : a * c = 1)
  (rightinvc : c * a = 1)
: b=c  := by
  Hint "Use `mul_one`"
  rw [<-mul_one b]
  Hint "Use `leftinvc`"
  rw [<-leftinvc]
  Hint "Use `assoc`"
  rw [<-mul_assoc]
  Hint "Use `rightinvb`"
  rw [rightinvb]
  Hint "Use `one_mul`"
  rw [one_mul]

NewTactic use rw rfl apply group constructor
NewTheorem And.intro mul_one mul_assoc one_mul
