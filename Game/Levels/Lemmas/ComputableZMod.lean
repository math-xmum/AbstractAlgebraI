import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Sort

section reprZMod

def tofin {n} (h: 0≠ n) (a : ZMod n) : Fin n :=
  match n with
  | 0 => by contradiction
  | n+1 => by
      unfold ZMod at a
      simp at a
      exact a


def finsettofin (a : Finset (ZMod n)) : Finset (Fin n) :=
match n with
 | 0 => Finset.empty
 | n+1 => by
      unfold ZMod at a
      simp only [Nat.add_eq, add_zero] at a
      exact a

instance {n : ℕ} : Repr (Finset (ZMod n)) where
  reprPrec s p := "{" ++ String.intercalate ", " ((Finset.sort (· ≤ ·) (finsettofin s)).map (fun x => toString (repr x))) ++ "}"


instance HAddtoHVAdd [HAdd A B C] [DecidableEq C] : HVAdd A (Finset B) (Finset C) where
  hVAdd a s := Finset.image (a + ·) s


end reprZMod



open Function Finset

variable {α : Type*}  {f : α → α} {x : α} [DecidableEq α]

abbrev G := ZMod 6

abbrev H := image (3 • · )  (univ: Finset (ZMod 6))

abbrev HH:Finset (Fin 6) := {0,3}

#eval H = HH


#eval (1 : ZMod 6) +ᵥ H
#eval (2 : ZMod 6) +ᵥ H
