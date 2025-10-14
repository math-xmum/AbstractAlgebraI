import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Defs


namespace Mul

variable {α β γ: Type*} [Mul α] [Mul β] [Add γ]

/--
An element `e` in a magma is an identity if for all elements `a` in the magma,
the multiplication of `e` with `a` (on either side) results in `a`.
In other words, `e` satisfies the following properties:
1. `e * a = a` for all `a`.
2. `a * e = a` for all `a`.
-/
abbrev isIdentity (one : α) := ∀ x, x * one = x ∧ one * x = x

/--
`isMulMap` is a predicate that checks whether a given function `f` between two magmas
preserves the multiplication operation. Specifically, for groups `α` and `β`, a function `f : α → β` satisfies `isMulMap f` if for all `x, y ∈ G`, the equation `f (x * y) = f x * f y` holds.
-/
@[to_additive]
abbrev isMulMap (f : α → β ) := ∀ x y, f (x * y) = f x * f y

abbrev isAddMulMap (f : γ → β ) := ∀ x y, f (x + y) = f x * f y

abbrev isMulAddMap (f : β → γ ) := ∀ x y, f (x * y) = f x + f y


end Mul

namespace Set
variable {α : Type*} [Mul α] (G : Set α) {β : Type*}
[Add β] (H : Set β)

/--
Let α be a type with Mul.
A subset of a magma `α` is a (sub)-magma if for all `x, y ∈ G`, the multiplication of `x` with `y` (on either side) results in an element in `G`.
-/
@[to_additive]
abbrev isMagma := ∀ {x y}, x ∈  G → y ∈ G → x * y ∈ G



class IsMagma where
  mul_mem : isMagma G


abbrev isCommutative [G.IsMagma]:= ∀ {x y}, x ∈  G → y ∈ G → x * y = y * x

class IsAddMagma where
  add_mem : isAddMagma H

instance instMagma [h : IsMagma G]: Mul G where
  mul := fun a b => ⟨a.1 * b.1, h.mul_mem a.2 b.2⟩

@[simp]
lemma IsMagma.mul_def [h : IsMagma G] : ∀ {a b : G }, a * b = ⟨a.1 * b.1, h.mul_mem a.2 b.2⟩ := by intros; rfl

instance instAddMagma [h : IsAddMagma H]: Add H where
  add:= fun a b => ⟨a.1 + b.1, h.add_mem a.2 b.2⟩


lemma IsAddMagma.add_def [h : IsAddMagma H] : ∀ {a b : H }, a + b = ⟨a.1 + b.1, h.add_mem a.2 b.2⟩ := by intros; rfl


@[to_additive]
abbrev isMulAssoc := ∀ {x y z}, x ∈ G → y ∈ G → z ∈ G → x * (y * z) = (x * y) * z

#check isAddAssoc


class IsSemigroup (G : Set α) extends IsMagma G where
  mul_assoc : isMulAssoc G



structure isOne (one : α) where
   one_mem : one ∈ G
   mul_one : ∀ x ∈ G, x * one = x
   one_mul : ∀ x ∈ G, one * x = x

class HasOne (G : Set α) where
  one : α
  isOne : G.isOne one

instance [h : HasOne G] : One G  where
  one := ⟨h.one, h.isOne.one_mem⟩


class IsMonoid (G : Set α) extends IsSemigroup G, HasOne G

/-
instance [H : IsMonoid G] : Monoid G  where
  mul_assoc := by
    intro a b c
    have H := H.mul_assoc a.2 b.2 c.2
    ext; simp [H]


class isInv [IsMagma G] (inv : G → G) where
  mul_inv : ∀ x ∈ G, x * inv x = one
  inv_mul : ∀ x ∈ G, inv x * x = one

class HasInv (G : Set α) where
  inv : α → α
  inv_mem : ∀ x ∈ G, inv x ∈ G
  mul_inv : ∀ x ∈ G, x * inv x = one
  inv_mul : ∀ x ∈ G, inv x * x = one

class IsGroup (G : Set α) extends IsMonoid G, HasInv G
-/
end Set


section inverse


/--
Suppose α is a monoid.
`b :  α ` is called a left inverse of `a` if `b * a = 1`.
-/
abbrev LeftInverse [Monoid α ](a b : α) := b * a = 1


/--
Suppose α is a monoid.
`b : α` is called a right inverse of `a` if `b * a = 1`.
-/
abbrev RightInverse [Monoid α ](a b : α) := a * b = 1

/--
Suppose α is a monoid.
`b : α` is called an inverse of `a` if it is both left and right inverse of `a`, i.e. `b * a = 1` and `a * b = 1`.
-/
abbrev Inverse [Monoid α ](a b : α) := LeftInverse a b ∧ RightInverse a b


end inverse


namespace Group

/--
The function defines a subgroup of a group formed by all elements that satisfy a predicate P.
One have to show `1 ∈ P` and `∀ {a b:G}, P a → P b → P (a * b⁻¹)`.
-/
def subgroup_make {G : Type*} [Group G] (P : G → Prop) (one_mem : P 1) (mul_inv_mem :∀ {a b:G}, P a → P b → P (a * b⁻¹)): Subgroup G where
  carrier := {a | P a}
  mul_mem' := sorry
  one_mem' := one_mem
  inv_mem' := by
    simp only [Set.mem_setOf_eq]
    intro a ha
    have := (mul_inv_mem one_mem ha)
    simp only [one_mul] at this
    exact this

/--
The function defines an additive subgroup of a group formed by all elements that satisfy a predicate P.
One have to show `0 ∈ P` and `∀ {a b:G}, P a → P b → P (a - b)`.
-/
def addsubgroup_make {G : Type*} [AddGroup G] (P : G → Prop) (zero_mem : P 0) (add_neg_mem :∀ {a b:G}, P a → P b → P (a - b)): AddSubgroup G where
  carrier := {a | P a}
  add_mem' := sorry
  zero_mem' := zero_mem
  neg_mem' := by
    simp only [Set.mem_setOf_eq]
    intro a ha
    have := (add_neg_mem zero_mem ha)
    simp only [zero_sub] at this
    exact this


end Group
