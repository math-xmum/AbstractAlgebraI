import Game.Metadata

import Game.Levels.Lemmas.Group

World "Monoid"

Level 2


Introduction "
Let us get familar with the definition of a monoid.

Let α be a type. Then all the functions from α to α form a monoid under composition.

For `f g : α → α`, we define `f * g := f ∘ g`.
"

variable {α : Type*}

Statement --(preamble := )
  : Monoid (α → α):= by
  let mul := fun (f g : α → α)  => (f ∘ g)
  refine {
    mul := mul
    mul_assoc := ?mul_assoc
    one := ?one
    one_mul := ?one_mul
    mul_one := ?mul_one
  }
  · Hint "This is just the associativity of composition.
  Use `exact Function.comp_assoc` to prove this.
  "
    exact Function.comp_assoc
  · Hint "The identity element is the function `id : α → α`."
    use id
  · Hint "Use `intro a` to introduce the element `a`."
    intro a
    Hint "This is the theorem called `Function.id_comp`.
    For technical reasons, you need to use `nth_rw 2 [<-Function.id_comp a]` to rewrite the right hand side."
    nth_rw 2 [<-Function.id_comp a]
    Hint "This is just the definition of `*`. Use `rfl` to prove this."
    rfl
  · Hint "Use `intro a` to introduce the element `a`."
    intro a
    Hint "This is the theorem called `Function.id_comp`.
    For technical reasons, you need to use `nth_rw 2 [<-Function.comp_id a]` to rewrite the right hand side."
    nth_rw 2 [<-Function.comp_id a]
    Hint "This is just the definition of `*`. Use `rfl` to prove this."
    rfl


NewTheorem Function.comp_assoc Function.id_comp Function.comp_id
