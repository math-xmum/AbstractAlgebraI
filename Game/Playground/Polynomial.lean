import Mathlib

/-
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Polynomial.X', and it does not have executable code
def x : Polynomial ℕ:= Polynomial.X

-/

section
namespace Finsupp'
variable {α : Type*} [DecidableEq α] [DecidableEq M]

section
variable [Zero M] [Zero N] [Zero P] [DecidableEq P]


def single (a : α)  (b :M): α →₀ M  where
  support := if b = 0 then ∅ else {a}
  toFun := fun i => if i = a  then b else 0
  mem_support_toFun := by
    intro i
    by_cases h : b = 0 <;> simp [h]

/-- `Finsupp.onFinset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
The function must be `0` outside of `s`. Use this when the set needs to be filtered anyways,
otherwise a better set representation is often available. -/
def onFinset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ M where
    support := s.filter (f · ≠ 0)
    toFun := f
    mem_support_toFun := by
      simpa


def zipWith (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  onFinset
    (g₁.support ∪ g₂.support)
    (fun a => f (g₁ a) (g₂ a))
    fun a (H : f _ _ ≠ 0) => by
      rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff, ← not_and_or]
      rintro ⟨h₁, h₂⟩; rw [h₁, h₂] at H; exact H hf

def mapRange [DecidableEq N] (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  onFinset g.support (f ∘ g) fun a => by
    rw [Finsupp.mem_support_iff, not_imp_not]; exact fun H => (congr_arg f H).trans hf

end

section

variable [AddZeroClass M]

#check add_zero

instance (priority := 6000) instAdd : Add (α →₀ M) :=
  ⟨Finsupp'.zipWith (fun (a b :M) => a + b ) (add_zero 0)⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : α →₀ M) = 0 := rfl

@[simp, norm_cast] lemma coe_add (f g : α →₀ M) : ⇑(f + g) = f + g := rfl

instance instAddZeroClass : AddZeroClass (α →₀ M) :=
   DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

@[simps]
noncomputable def coeFnAddHom : (α →₀ M) →+ α → M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
end


section

variable [AddMonoid M]

/-- Note the general `SMul` instance for `Finsupp` doesn't apply as `ℕ` is not distributive
unless `F i`'s addition is commutative. -/
instance instNatSMul : SMul ℕ (ι →₀ M) where smul n v := Finsupp'.mapRange (n • ·) (nsmul_zero _) v


instance (priority := 1000) instAddMonoid : AddMonoid (α →₀ M) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl


end


instance (priority := 1000) instAddCommMonoid [AddCommMonoid M] : AddCommMonoid (α →₀ M) :=
  DFunLike.coe_injective.addCommMonoid
    DFunLike.coe coe_zero coe_add (fun _ _ => rfl)


section

variable [Semiring k] [Mul G] [DecidableEq G] [DecidableEq k]

open BigOperators in
def mul'' (f g : MonoidAlgebra k G) :  MonoidAlgebra k G :=
 by
  unfold MonoidAlgebra at *
  exact Finset.sum  f.support <| fun a =>  Finset.sum   g.support fun b =>  (Finsupp'.single (a * b) (f a * g b))

instance (priority := 6000) instMul : Mul (MonoidAlgebra k G) where
  mul := mul''

end

section

variable [Semiring k] [Add G] [DecidableEq G] [DecidableEq k]

open BigOperators in
def amul'' (f g : MonoidAlgebra k G) :  MonoidAlgebra k G :=
 by
  unfold MonoidAlgebra at *
  exact Finset.sum  f.support <| fun a =>  Finset.sum   g.support fun b =>  (Finsupp'.single (a + b) (f a * g b))

instance (priority := 6000) instAddMul : Mul (MonoidAlgebra k G) where
  mul := amul''

end


end Finsupp'
end




section
open Finsupp'
variable [Semiring R] [DecidableEq R]



instance (priority := 6000) Polynomial.instAdd : Add (Polynomial R) where
  add := fun x y =>
    by
      let a := x.1
      let b := y.1
      rw [AddMonoidAlgebra] at *
      exact ⟨a + b⟩


#synth Mul (Polynomial R)

instance (priority := 6000) Polynomial.instMul' : Mul (Polynomial R) where
  mul := fun x y =>
    by
      let a := x.1
      let b := y.1
      rw [AddMonoidAlgebra] at *
      exact ⟨Finsupp'.amul'' a  b⟩


def C : R → Polynomial R :=
  fun r => ⟨Finsupp'.single 0 r⟩
def X := Polynomial.ofFinsupp <| Finsupp'.single 1 (1:R)

end


section

def x : Polynomial ℕ:= X

#eval (C 2) + (C 3)
#eval ((x + x + x) : Polynomial ℕ)
#eval (C 2 + (x+x+x)*x + x : Polynomial ℕ)
#eval (C 1 + x) * (C 1 + x)


example : (x + x) * x =  x * (x + x) := by decide

example : (C 1 + x) * (C 1 + x) = C 1 + x + x + x*x := by decide


end
