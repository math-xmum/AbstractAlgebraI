import Mathlib
import Qq
import Lean


open Qq Lean Meta

class ToExprM (α : Type u) where
  /-- The reflected version of `inst`. -/
  toExprM : α → MetaM Expr
  toTypeExprM : MetaM Expr

instance [h:ToExpr α] : ToExprM α where
  toExprM := fun x => pure (toExpr x)
  toTypeExprM := pure (h.toTypeExpr)

open Lean.Meta

def  toExprAux {α : Type u} [ToLevel.{u}] [inst:ToExprM α]: List α  → MetaM Expr := fun x => do
  let type ← ToExprM.toTypeExprM α
  match x with
  | []    => pure <| mkAppN (.const ``Finset.empty [toLevel.{u}]) #[type]
  | a::as => mkAppM ``Insert.insert #[(←inst.toExprM a),(←toExprAux as)]



unsafe instance Finset.toExprM
    {α : Type u} [ToLevel.{u}] [ToExprM α] [DecidableEq α] : ToExprM (Finset α) where
  toTypeExprM := do
    let type ← ToExprM.toTypeExprM α
    mkAppM ``Finset #[type]
  toExprM := fun x => (toExprAux x.val.unquot)


syntax (name := eval_exprm) "evalm% " term : term

@[term_elab eval_exprm, inherit_doc eval_exprm]
unsafe def elabEvalExpr : Lean.Elab.Term.TermElab
| `(term| evalm% $stx) => fun exp => do
  let e ← Lean.Elab.Term.elabTermAndSynthesize stx exp
  let e ← instantiateMVars e
  logInfo m!"{← ppExpr e}"
  let type ← inferType e
  let type ← whnf type
  logInfo m!"{← ppExpr type}"
  let ee ← Meta.mkAppM ``ToExprM.toExprM #[e]
  let eetype ← inferType ee
  logInfo m!"{← ppExpr eetype}"
  let ee ← Lean.Meta.evalExpr (MetaM Expr) eetype ee (safety := .unsafe)
  --Lean.Meta.evalExpr Expr q(Expr) e (safety :=.unsafe)
  return (←ee)
| _ => fun _ => Elab.throwUnsupportedSyntax


#check List.cons
#check Insert.insert
#check Finset.empty

#check evalm% ({} : Finset ℕ )
#check evalm% ({({2^10,1} : Finset ℕ),{2^3,2^5}}: Finset (Finset ℕ))

lemma a: ({2^10,1} : Finset ℕ) = evalm% ({2^10,1} : Finset ℕ):= by rfl

def twopowers (n : ℕ) : Finset ℕ := match n with
| 0 => {1}
| n+1 => {2^(n+1)} ∪ twopowers n

#eval twopowers 10

example (x : ℕ ): x∈ twopowers 10 → x=1 ∨ x %2 =0:= by
  intro hx
  have hh : twopowers 10 = evalm% twopowers 10 := by native_decide
  rw [hh] at hx
  repeat rw [Finset.mem_insert] at hx
  casesm* _ ∨ _
  all_goals try simp [h]
  exfalso
  exact Finset.not_mem_empty _ h

#check a
