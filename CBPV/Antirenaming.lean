import CBPV.Evaluation
import CBPV.Rejoin
import CBPV.Typing

open Nat Val Com

/-*-----------------------------------------------------------
  Antirenaming: If a jump-renamed m reduces to n,
  then n must be some renamed computation that m reduces to;
  we require that m be well-scoped wrt jump variables.
-----------------------------------------------------------*-/

theorem antirenameJ {δ δ' m n'} {ξ : Fin δ → Fin δ'} (r : renameJCom ξ m ⇒ n') :
  ∃ n, n' = renameJCom ξ n ∧ m ⇒ n := by
  generalize e : renameJCom ξ m = m' at r
  induction r generalizing δ m
  case π =>
    cases m <;> injection e
    case force v _ e =>
      cases v <;> injection e; subst_vars
      exact ⟨_, renameWeakenJ.symm, .π⟩
  case β =>
    cases m <;> injection e
    case app m _ _ em _ =>
      cases m <;> injection em; subst_vars
      exact ⟨_, renameWeakenJ.symm, .β⟩
  case ζ =>
    cases m <;> injection e
    case letin m₁ m₂ _ em₁ _ =>
      cases m₁ <;> injection em₁; subst_vars
      exact ⟨_, renameJSubst ξ (_ +: var) m₂, .ζ⟩
  case ιl | ιr =>
    cases m <;> injection e
    case case v _ _ _ ev _ _ =>
      cases v <;> injection ev; subst_vars
      exact ⟨_, renameJSubst ξ (_ +: var) _, by constructor⟩
  case π1 | π2 =>
    cases m <;> injection e
    case _ m _ e =>
      cases m <;> injection e; subst_vars
      exact ⟨_, renameWeakenJ.symm, by constructor⟩
  case ret | lam | prod =>
    cases m <;> injection e
    case join m₁ m₂ _ em₁ em₂ =>
      cases m₂ <;> injection em₂; subst_vars
      exact ⟨_, rfl, by constructor⟩
  case app r _ | letin r _ | fst r _ | snd r _ =>
    cases m <;> injection e; subst_vars
    exact ⟨_, rfl, by constructor; exact r⟩
  case γ =>
    cases m <;> injection e
    case join m₁ m₂ _ em₁ em₂ =>
      cases m₂ <;> injection em₂
      case jump v j _ ej ev =>
        subst ev em₁
        match j with
        | ⟨0, _⟩ => exact ⟨_, renameJSubst ξ (v +: var) m₁, .γ⟩
        | ⟨j + 1, _⟩ => cases ej
  case join't =>
    cases m <;> injection e
    case join m₁ m₂ _ em₁ em₂ =>
      cases m₂ <;> injection em₂
      case jump v j _ ej ev =>
      subst ev
      match j with
      | ⟨0, _⟩ => cases ej
      | ⟨j + 1, lt⟩ =>
        rw [← Fin.succ_mk _ _ (lt_of_succ_lt_succ lt)]
        simp [liftJ] at ej; subst ej
        exact ⟨_, rfl, .join't⟩
  case join =>
    cases m <;> injection e
    case join ih m₁ m₂ _ em₁ em₂ =>
      let ⟨m₂', em₂, r⟩ := ih em₂
      subst em₁ em₂
      exact ⟨_, rfl, .join r⟩

/-* Corollary: A jump-weakened join body can drop the join point *-/

theorem Eval.wkJoin {δ} {js : J δ} {m₁ m₂ m} (r : .rejoin (.join m₁ (renameJCom Fin.succ m₂)) js ⇒ m) :
  (m = .rejoin m₂ js) ∨ (∃ m₂', m₂ ⇒ m₂' ∧ m = .rejoin (.join m₁ (renameJCom Fin.succ m₂')) js) := by
  let ⟨_, r, e⟩ := r.rejoin_inv
  generalize erename : renameJCom Fin.succ m₂ = m₂' at r
  cases r
  case join r =>
    subst erename
    let ⟨n, en, rn⟩ := antirenameJ r
    subst en; exact .inr ⟨_, rn, e⟩
  all_goals cases m₂ <;> injection erename
  case γ ej _ => cases ej
  case ret e' | lam e' => subst e'; exact .inl e
  case prod e₁ e₂ => subst e₁ e₂; exact .inl e
  case join't ej ev => rw [Fin.succ_inj.mp ej]; subst ev; exact .inl e

theorem Norm.wkJoin {δ} {js : J δ} {m₁ m₂ n} (r : rejoin (.join m₁ (renameJCom Fin.succ m₂)) js ⇓ₙ n) :
  ∃ m₂', m₂ ⇒⋆ m₂' ∧ rejoin (.join m₁ (renameJCom Fin.succ m₂)) js ⇒⋆ rejoin m₂' js ∧ rejoin m₂' js ⇒⋆ n := by
  cases r with | _ rn nfn =>
  generalize e : rejoin (.join m₁ (renameJCom Fin.succ m₂)) js = m at rn
  induction rn generalizing m₂
  case refl => subst e; cases nfn.rejoin't (by simp)
  case trans r rs ih =>
    subst e
    match r.wkJoin with
    | .inl e =>
      subst e
      let ⟨_, r, e⟩ := r.rejoin_inv
      refine ⟨_, .refl, ?_, rs⟩; rw [e]
      exact .rejoin (.once r)
    | .inr ⟨n, rn, en⟩ =>
      subst en
      have ⟨_, rn', rjoin, rs⟩ := ih nfn rfl
      refine ⟨_, .trans rn rn', .trans (.rejoin (.join rn.renameJ)) rjoin, rs⟩
