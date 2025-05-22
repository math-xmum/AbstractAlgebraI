import Mathlib

open Equiv
open Function

#eval permsOfFinset (Finset.univ : Finset (Fin 3))
#eval (Finset.univ : Finset (Perm (Fin 3)))

lemma elemsperm : (Finset.univ : Finset (Perm (Fin 3))) = {1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]} := by native_decide


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
