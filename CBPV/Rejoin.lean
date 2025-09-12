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

@[reducible] def J := List Com

@[simp]
def Com.rejoin (m : Com) : J → Com
  | .nil => m
  | .cons n js => rejoin (join n m) js

theorem Eval.rejoin {m n js} (r : m ⇒ n) : rejoin m js ⇒ rejoin n js := by
  induction js generalizing m n
  case nil => exact r
  case cons ih => simp; exact ih (.join r)

theorem Eval.rejoin_inv {js m₁ m₂ m} (r : .rejoin (.join m₁ m₂) js ⇒ m) :
  ∃ m', .join m₁ m₂ ⇒ m' ∧ m = .rejoin m' js := by
  induction js generalizing m₁ m₂
  case nil => simpa
  case cons ih =>
    let ⟨_, r, e⟩ := ih r
    cases r with | join r => exact ⟨_, r, e⟩

theorem Evals.rejoin {m n js} (r : m ⇒⋆ n) : rejoin m js ⇒⋆ rejoin n js := by
  induction r
  case refl => rfl
  case trans r _ rs => exact .trans (r.rejoin) rs

theorem nf.rejoinDrop {m js} : nf m → rejoin m js ⇒⋆ m := by
  intro nfm; mutual_induction m generalizing nfm js
  all_goals simp at nfm
  case lam | ret | prod =>
    induction js <;> simp [RTC.refl]
    case cons ih =>
      refine .trans' (Evals.rejoin (.once ?_)) ih; constructor

theorem nf.rejoin't {js m} (nfmn't : ¬ nf m) : ¬ nf (rejoin m js) := by
  induction js generalizing m
  case nil => exact nfmn't
  case cons ih => apply ih; simp

theorem Norm.bwdsRejoin {m n n' js} (r : m ⇒⋆ n) : n ⇓ₙ n' → rejoin m js ⇓ₙ n'
  | ⟨r', nfn⟩ => ⟨.trans' (Evals.rejoin (.trans' r r')) nfn.rejoinDrop, nfn⟩
