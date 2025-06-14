import Mathlib
import Game.Playground.Evalm

open Equiv
open Function

#eval permsOfFinset (Finset.univ : Finset (Fin 3))
#eval (Finset.univ : Finset (Perm (Fin 3)))

lemma elemsperm : (Finset.univ : Finset (Perm (Fin 3)))
= {1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]}
:= by native_decide



--lemma elemsperm1 : (Finset.univ : Finset (Perm (Fin 3))) = eval% (Finset.univ : Finset (Perm (Fin 3))) := by rfl

#eval (Finset.univ : Finset (alternatingGroup (Fin 3)))

instance {α : Type*} [DecidableEq α] [Fintype α] (x : Perm α) : Decidable (x ∈ alternatingGroup α) := Perm.sign.decidableMemKer _


abbrev finsetA4 : Finset (alternatingGroup (Fin 4)) := { 1,
 ⟨c[1, 2, 3],by decide⟩,
 ⟨c[1, 3, 2],by decide⟩,
 ⟨c[0, 1, 2],by decide⟩,
 ⟨c[0, 2, 1],by decide⟩,
 ⟨c[0, 3, 2],by decide⟩,
 ⟨c[0, 2, 3],by decide⟩,
 ⟨c[0, 1, 3],by decide⟩,
 ⟨c[0, 3, 1],by decide⟩,
 ⟨c[0, 1] * c[2,3],by decide⟩,
 ⟨c[0, 2] * c[1,3],by decide⟩,
 ⟨c[0, 3] * c[1,2],by decide⟩
 }

lemma alter4': finsetA4 = (Finset.univ : Finset (alternatingGroup (Fin 4))) := by  native_decide



def twopowers (n : ℕ) : Finset ℕ := match n with
| 0 => {1}
| n+1 => {2^(n+1)} ∪ twopowers n

#eval twopowers 3 --  {8, 4, 2, 1}

lemma tp3 : twopowers 3 = {1,2,4,8} := by native_decide

-- lemma tp3' : twopowers 3 = eval% twopowers 3
-- := by native_decide

lemma tp3'' : twopowers 3 = evalm% twopowers 3
:= by native_decide
#print tp3''
-- theorem tp3'' : twopowers 3 = {8, 4, 2, 1} := ...


example (x : ℕ ): x ∈ twopowers 10 → x=1 ∨ x %2 =0:= by
  intro hx
  have hh : twopowers 10 = evalm% twopowers 10 := by native_decide
  rw [hh] at hx
  fin_cases hx <;> simp
