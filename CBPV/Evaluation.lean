import CBPV.RTC
import CBPV.Syntax

open Nat Val Com

/-*-----------------------
  Single-step evaluation
-----------------------*-/

section
set_option hygiene false
local infix:40 "⇒" => Eval
inductive Eval : ∀ {δ}, Com δ → Com δ → Prop where
  -- reduction steps
  | π {δ m} : force (thunk m) ⇒ weakenJCom δ m
  | β {δ m v} : app (lam m) v ⇒ weakenJCom δ (m⦃v⦄)
  | ζ {v m} : letin (ret v) m ⇒ m⦃v⦄
  | ιl {v m n} : case (inl v) m n ⇒ m⦃v⦄
  | ιr {v m n} : case (inr v) m n ⇒ n⦃v⦄
  | π1 {δ m n} : fst (prod m n) ⇒ weakenJCom δ m
  | π2 {δ m n} : snd (prod m n) ⇒ weakenJCom δ n
  | γ {m v} : join m (jump 0 v) ⇒ m⦃v⦄
  -- drop joins
  | ret {m v} : join m (ret v) ⇒ ret v
  | lam {m n} : join m (lam n) ⇒ lam n
  | prod {m n₁ n₂} : join m (prod n₁ n₂) ⇒ prod n₁ n₂
  | join't {j m v} : join m (jump (j.succ) v) ⇒ (jump j v)
  -- congruence rules
  | app {m m' v} :
    m ⇒ m' →
    ------------------
    app m v ⇒ app m' v
  | letin {m m' n} :
    m ⇒ m' →
    ----------------------
    letin m n ⇒ letin m' n
  | fst {m m'} :
    m ⇒ m' →
    ----------------
    fst m ⇒ fst m'
  | snd {m m'} :
    m ⇒ m' →
    ----------------
    snd m ⇒ snd m'
  | join {m n n'} :
    n ⇒ n' →
    --------------------
    join m n ⇒ join m n'
end
infix:40 "⇒" => Eval

namespace Eval

theorem renameJ {δ δ' m n} {ξ : Fin δ → Fin δ'} (r : m ⇒ n) : renameJCom ξ m ⇒ renameJCom ξ n := by
  induction r generalizing δ' <;> simp
  all_goals try rw [← renameJSubst]
  all_goals try rw [renameWeakenJ]
  all_goals constructor <;> apply_assumption

theorem weakenJ {δ δ' m n} (r : m ⇒ n) : @weakenJCom δ δ' m ⇒ @weakenJCom δ δ' n := renameJ r

theorem det {δ} {m n₁ n₂ : Com δ} (r₁ : m ⇒ n₁) (r₂ : m ⇒ n₂) : n₁ = n₂ := by
  induction r₁
  case join't j _ _ =>
    generalize e : Fin.succ j = j' at r₂
    cases r₂
    case γ => injection e; contradiction
    case join v n r => cases r
    case join't =>
      injection e with e; injection e with e
      cases j; subst e; rfl
  all_goals cases r₂; try rfl
  case fst.fst ih _ r | snd.snd ih _ r => rw [ih r]
  all_goals try apply_rules [appCong, letinCong, prodCong, joinCong]
  all_goals rename _ ⇒ _ => r; cases r

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

end Eval

/-*----------------------
  Multi-step evaluation
----------------------*-/

@[reducible] def Evals {δ} := RTC (@Eval δ)
infix:40 "⇒⋆" => Evals

namespace Evals

theorem app {δ m n v} (r : m ⇒⋆ n) : @app δ m v ⇒⋆ @app δ n v := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.app r) ih

theorem letin {δ m m' n} (r : m ⇒⋆ m') : @letin δ m n ⇒⋆ @letin δ m' n := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.letin r) ih

theorem fst {δ m m'} (r : m ⇒⋆ m') : @fst δ m ⇒⋆ @fst δ m' := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.fst r) ih

theorem snd {δ m m'} (r : m ⇒⋆ m') : @snd δ m ⇒⋆ @snd δ m' := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.snd r) ih

theorem join {δ m n n'} (r : n ⇒⋆ n') : @join δ m n ⇒⋆ @join δ m n' := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.join r) ih

theorem ret_inv {δ v m} (r : @ret δ v ⇒⋆ m) : ret v = m := by
  generalize e : ret v = n at r
  induction r generalizing v <;> subst e
  case refl => rfl
  case trans r => cases r

theorem lam_inv {δ m n} (r : @lam δ m ⇒⋆ n) : lam m = n := by
  generalize e : lam m = m' at r
  induction r generalizing m <;> subst e
  case refl => rfl
  case trans r => cases r

theorem prod_inv {δ m₁ m₂ n} (r : @prod δ m₁ m₂ ⇒⋆ n) : prod m₁ m₂ = n := by
  generalize e : prod m₁ m₂ = m at r
  induction r generalizing m₁ m₂ <;> subst e
  case refl => rfl
  case trans r => cases r

theorem jump_inv {δ j v n} (r : @jump δ j v ⇒⋆ n) : jump j v = n := by
  generalize e : jump j v = m at r
  induction r generalizing j v <;> subst e
  case refl => rfl
  case trans r => cases r

theorem weakenJ {δ δ' m n} (r : m ⇒⋆ n) : @weakenJCom δ δ' m ⇒⋆ @weakenJCom δ δ' n := by
  induction r
  case refl => rfl
  case trans r _ ih => exact .trans (.weakenJ r) ih

end Evals

/-*----------------------------
  Normal forms and evaluation
----------------------------*-/

@[simp]
def nf {δ} : Com δ → Prop
  | lam _ | ret _ | prod _ _ => True
  | _ => False

theorem nf.stepn't {δ} {m n : Com δ} (nfm : nf m) : ¬ m ⇒ n := by
  cases m <;> simp at *
  all_goals intro r; cases r

theorem nf.steps {δ} {m n : Com δ} (nfm : nf m) (r : m ⇒⋆ n) : m = n := by
  cases r
  case refl => rfl
  case trans r _ => cases nfm.stepn't r

def Norm {δ} (m n : Com δ) := m ⇒⋆ n ∧ nf n
infix:40 "⇓ₙ" => Norm

theorem Evals.merge {δ} {m₁ m₂ n : Com δ} (rm : m₁ ⇒⋆ m₂) : m₁ ⇓ₙ n → m₂ ⇒⋆ n
  | ⟨rn, nfn⟩ => by
    induction rm generalizing n
    case refl => assumption
    case trans r _ ih =>
      cases rn
      case refl => cases nfn.stepn't r
      case trans r' rn => rw [Eval.det r r'] at ih; exact ih rn nfn

namespace Norm

@[refl] theorem refl {δ} {m : Com δ} (nfm : nf m) : m ⇓ₙ m := by exists .refl

theorem bwds {δ} {m m' n : Com δ} (r : m ⇒⋆ m') : m' ⇓ₙ n → m ⇓ₙ n
  | ⟨rn, nfn⟩ => ⟨.trans' r rn, nfn⟩

theorem join {δ} {m n₁ n₂ : Com δ} : m ⇓ₙ n₁ → m ⇓ₙ n₂ → n₁ = n₂
  | ⟨rn₁, nfn₁⟩, rn₂ => nfn₁.steps (rn₁.merge rn₂)

end Norm

/-*---------------------
  Strong normalization
---------------------*-/

inductive SN {δ} : Com δ → Prop where
  | sn : ∀ m, (∀ n, m ⇒ n → SN n) → SN m

theorem SN.nf {δ m} (nfm : nf m) : @SN δ m := by
  constructor; intro n r; cases nfm.stepn't r

theorem Evals.sn {δ m n} (r : m ⇒⋆ n) (nfn : nf n) : @SN δ m := by
  induction r
  case refl => exact .nf nfn
  case trans r _ ih => constructor; intro _ r'; rw [← Eval.det r r']; exact ih nfn
