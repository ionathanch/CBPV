import CBPV.Evaluation

open Nat Val Com

/-*---------------------------------------------------------------
  Join stacks and rejoining

  This is a proof widget used for the logical relations.
  Join stacks resemble just the join frames of CK stacks:
    J ::= □ | J[join j = γx. m in □]

  Rejoining a join stack onto a computation
  is dismantling the stack, or plugging into the innermost hole.
  The final computation must then have the following shape:
    join j₁ = γx. m₁ in ... join jᵢ = γx. mᵢ in m

  Join stacks satisfy two important properties:
  * (`rejoinDrop`): Rejoined terminals reduce to those terminals
    with the entire join stack dropped;
  * Rejoining (jump j v) drops j joins (as a de Bruijn index).

  The latter resembles the following:
    J[join 1 = γx. m₁ in ... join j = γx. mⱼ in jump j v]
    ⇒⋆ J[jump 0 v]
  Instead of proving it here,
  it gets combined with the logical relations,
  e.g. `ClosedSemantics.rejoinJump`.

  These definitions are isolated here instead of
  incorporated into Syntax and Evaluation
  because they are not really part of the surface syntax
  or evaluation rules of the language.
---------------------------------------------------------------*-/

inductive J : Nat → Type where
  | nil : J 0
  | cons {δ} : Com δ → J δ → J (δ + 1)

@[simp]
def Com.rejoin {δ} (m : Com δ) : J δ → Com 0
  | .nil => m
  | .cons n js => rejoin (join n m) js

theorem Eval.rejoin {δ m n js} (r : m ⇒ n) : @rejoin δ m js ⇒ @rejoin δ n js := by
  induction js
  case nil => exact r
  case cons ih => simp; exact ih (.join r)

theorem Eval.rejoin_inv {δ js m₁ m₂ m} (r : .rejoin (@Com.join δ m₁ m₂) js ⇒ m) :
  ∃ m', .join m₁ m₂ ⇒ m' ∧ m = .rejoin m' js := by
  induction js
  case nil => simpa
  case cons ih =>
    let ⟨_, r, e⟩ := ih r
    cases r with | join r => exact ⟨_, r, e⟩

theorem Evals.rejoin {δ m n js} (r : m ⇒⋆ n) : @rejoin δ m js ⇒⋆ @rejoin δ n js := by
  induction r
  case refl => rfl
  case trans r _ rs => exact .trans (r.rejoin) rs

theorem nf.rejoinDrop {δ m js} : nf m → rejoin (weakenJCom δ m) js ⇒⋆ m := by
  intro nfm; cases m
  all_goals simp at nfm
  case lam | ret | prod =>
    induction δ <;> cases js <;> simp [weakenJCom, RTC.refl]
    case succ ih _ _ =>
      refine .trans' (Evals.rejoin (.once ?_)) ih; constructor

theorem nf.rejoin't {δ m js} (nfmn't : ¬ @nf δ m) : ¬ nf (rejoin m js) := by
  induction js
  case nil => exact nfmn't
  case cons ih => apply ih; simp

theorem Norm.bwdsRejoin {δ m n n' js} (r : m ⇒⋆ n) : n ⇓ₙ n' → rejoin (weakenJCom δ m) js ⇓ₙ n'
  | ⟨r', nfn⟩ =>
    ⟨.trans' (Evals.rejoin (Evals.weakenJ (.trans' r r'))) nfn.rejoinDrop, nfn⟩
