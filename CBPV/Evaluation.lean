import CBPV.RTC
import CBPV.Syntax

open Val Com

/-*-----------------------
  Single-step evaluation
-----------------------*-/

section
set_option hygiene false
local infix:40 "⇒" => Eval
inductive Eval : Com → Com → Prop where
  | μ {m} : force (thunk m) ⇒ m
  | β {m v} : app (lam m) v ⇒ m⦃v⦄
  | ζ {v m} : letin (ret v) m ⇒ m⦃v⦄
  | ιl {v m n} : case (inl v) m n ⇒ m⦃v⦄
  | ιr {v m n} : case (inr v) m n ⇒ n⦃v⦄
  | π1 {m n} : fst (prod m n) ⇒ m
  | π2 {m n} : snd (prod m n) ⇒ n
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
end
infix:40 "⇒" => Eval

-- Single-step evaluation is deterministic
theorem Eval.det {m n₁ n₂} (r₁ : m ⇒ n₁) (r₂ : m ⇒ n₂) : n₁ = n₂ := by
  induction r₁ generalizing n₂
  all_goals cases r₂; try rfl
  case fst.fst ih _ r | snd.snd ih _ r => rw [ih r]
  all_goals try apply_rules [appCong, letinCong, prodCong]
  all_goals rename _ ⇒ _ => r; cases r

/-*----------------------
  Multi-step evaluation
----------------------*-/

@[reducible] def Evals := RTC Eval
infix:40 "⇒⋆" => Evals

namespace Evals

theorem app {m n v} (r : m ⇒⋆ n) : app m v ⇒⋆ app n v := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.app r) ih

theorem letin {m m' n} (r : m ⇒⋆ m') : letin m n ⇒⋆ letin m' n := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.letin r) ih

theorem fst {m m'} (r : m ⇒⋆ m') : fst m ⇒⋆ fst m' := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.fst r) ih

theorem snd {m m'} (r : m ⇒⋆ m') : snd m ⇒⋆ snd m' := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.snd r) ih

theorem ret_inv {v m} (r : ret v ⇒⋆ m) : ret v = m := by
  generalize e : ret v = n at r
  induction r generalizing v <;> subst e
  case refl => rfl
  case trans r => cases r

theorem lam_inv {m n} (r : lam m ⇒⋆ n) : lam m = n := by
  generalize e : lam m = m' at r
  induction r generalizing m <;> subst e
  case refl => rfl
  case trans r => cases r

theorem prod_inv {m₁ m₂ n} (r : prod m₁ m₂ ⇒⋆ n) : prod m₁ m₂ = n := by
  generalize e : prod m₁ m₂ = m at r
  induction r generalizing m₁ m₂ <;> subst e
  case refl => rfl
  case trans r => cases r

end Evals

/-*----------------------------
  Normal forms and evaluation
----------------------------*-/

@[simp]
def nf : Com → Prop
  | lam _ | ret _ | prod _ _ => True
  | force _ | app _ _ | letin _ _ | case _ _ _ | fst _ | snd _ => False

theorem nf.stepn't {m n} (nfm : nf m) : ¬ m ⇒ n := by
  cases m <;> simp at *
  all_goals intro r; cases r

theorem nf.steps {m n} (nfm : nf m) (r : m ⇒⋆ n) : m = n := by
  cases r
  case refl => rfl
  case trans r _ => cases nfm.stepn't r

def Norm (m n : Com) := m ⇒⋆ n ∧ nf n
infix:40 "⇓ₙ" => Norm

theorem Evals.merge {m₁ m₂ n} (rm : m₁ ⇒⋆ m₂) : m₁ ⇓ₙ n → m₂ ⇒⋆ n
  | ⟨rn, nfn⟩ => by
    induction rm generalizing n
    case refl => assumption
    case trans r _ ih =>
      cases rn
      case refl => cases nfn.stepn't r
      case trans r' rn => rw [Eval.det r r'] at ih; exact ih rn nfn

namespace Norm

@[refl] theorem refl {m} (nfm : nf m) : m ⇓ₙ m := by exists .refl

theorem bwds {m m' n} (r : m ⇒⋆ m') : m' ⇓ₙ n → m ⇓ₙ n
  | ⟨rn, nfn⟩ => ⟨.trans' r rn, nfn⟩

theorem join {m n₁ n₂} : m ⇓ₙ n₁ → m ⇓ₙ n₂ → n₁ = n₂
  | ⟨rn₁, nfn₁⟩, rn₂ => nfn₁.steps (rn₁.merge rn₂)

end Norm

/-*---------------------
  Strong normalization
---------------------*-/

inductive SN : Com → Prop where
  | sn : ∀ m, (∀ n, m ⇒ n → SN n) → SN m

theorem Norm.sn {m n} : m ⇓ₙ n → SN m
  | ⟨r, nfn⟩ => by
    induction r
    case refl => constructor; intro _ r; cases nfn.stepn't r
    case trans r _ ih => constructor; intro _ r'; rw [← Eval.det r r']; exact ih nfn
