import CBPV.RTC
import CBPV.Syntax

open Nat Val Com

/-*-----------------------
  Single-step evaluation
-----------------------*-/

section
set_option hygiene false
local infix:40 "⇒" => Eval
inductive Eval : Com → Com → Prop where
  -- reduction steps
  | π {m} : force (thunk m) ⇒ m
  | β {m v} : app (lam m) v ⇒ m⦃v⦄
  | ζ {v m} : letin (ret v) m ⇒ m⦃v⦄
  | ιl {v m n} : case (inl v) m n ⇒ m⦃v⦄
  | ιr {v m n} : case (inr v) m n ⇒ n⦃v⦄
  | π1 {m n} : fst (prod m n) ⇒ m
  | π2 {m n} : snd (prod m n) ⇒ n
  | γ {m v} : join m (jump 0 v) ⇒ m⦃v⦄
  -- drop joins
  | ret {m v} : join m (ret v) ⇒ ret v
  | lam {m n} : join m (lam n) ⇒ lam n
  | prod {m n₁ n₂} : join m (prod n₁ n₂) ⇒ prod n₁ n₂
  | join't {j m v} : join m (jump (j + 1) v) ⇒ jump j v
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

-- Single-step evaluation is deterministic
theorem Eval.det {m n₁ n₂} (r₁ : m ⇒ n₁) (r₂ : m ⇒ n₂) : n₁ = n₂ := by
  induction r₁ generalizing n₂
  all_goals cases r₂; try rfl
  case fst.fst ih _ r | snd.snd ih _ r => rw [ih r]
  all_goals try apply_rules [appCong, letinCong, prodCong, joinCong]
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

theorem join {m n n'} (r : n ⇒⋆ n') : join m n ⇒⋆ join m n' := by
  induction r
  case refl => exact .refl
  case trans r _ ih => exact .trans (.join r) ih

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

theorem jump_inv {j v n} (r : jump j v ⇒⋆ n) : jump j v = n := by
  generalize e : jump j v = m at r
  induction r generalizing j v <;> subst e
  case refl => rfl
  case trans r => cases r

end Evals

-- Multi-step reduction is confluent trivially by determinism
theorem confluence {m n₁ n₂} (r₁ : m ⇒⋆ n₁) (r₂ : m ⇒⋆ n₂) : ∃ m', n₁ ⇒⋆ m' ∧ n₂ ⇒⋆ m' := by
  induction r₁ generalizing n₂
  case refl => exact ⟨n₂, r₂, .refl⟩
  case trans r₁ rs₁ ih =>
    cases r₂
    case refl => exact ⟨_, .refl, .trans r₁ rs₁⟩
    case trans r₂ rs₂ => rw [Eval.det r₁ r₂] at *; exact ih rs₂

/-*----------------------------
  Normal forms and evaluation
----------------------------*-/

@[simp]
def nf : Com → Prop
  | lam _ | ret _ | prod _ _ => True
  | _ => False

theorem nf.stepn't {m n} (nfm : nf m) : ¬ m ⇒ n := by
  cases m <;> simp at *
  all_goals intro r; cases r

theorem nf.steps {m n} (nfm : nf m) (r : m ⇒⋆ n) : m = n := by
  cases r
  case refl => rfl
  case trans r _ => cases nfm.stepn't r

def Norm (m n : Com) := m ⇒⋆ n ∧ nf n
infix:40 "⇓ₙ" => Norm

namespace Norm

@[refl] theorem refl {m} (nfm : nf m) : m ⇓ₙ m := by exists .refl

theorem bwds {m m' n} (r : m ⇒⋆ m') : m' ⇓ₙ n → m ⇓ₙ n
  | ⟨rn, nfn⟩ => ⟨.trans' r rn, nfn⟩

theorem join {m n₁ n₂} : m ⇓ₙ n₁ → m ⇓ₙ n₂ → n₁ = n₂
  | ⟨rn₁, nfn₁⟩, ⟨rn₂, nfn₂⟩ =>
    let ⟨n', rn₁', rn₂'⟩ := confluence rn₁ rn₂
    by rw [nfn₁.steps rn₁', nfn₂.steps rn₂']

theorem dropJoin {n n'} : n ⇓ₙ n' → ∀ m, .join m n ⇓ₙ n'
  | ⟨rn, nfn⟩, m => by
    cases n' <;> simp at nfn
    all_goals refine ⟨.trans' (Evals.join rn) (.once ?_), nfn⟩; constructor

theorem join_inv' {m₁ m₂ n} (r : .join m₁ m₂ ⇓ₙ n) :
  ∃ n', m₂ ⇒⋆ n' ∧ (nf n' ∨ ∃ j v, n' = jump j v) := by
  let ⟨r, nfn⟩ := r
  generalize e : Com.join m₁ m₂ = m₁' at r
  induction r generalizing m₁ m₂ <;> subst e
  case refl => cases nfn
  case trans ih r =>
    cases r
    case ret | lam | prod => exact ⟨_, .refl, .inl ⟨⟩⟩
    case γ | join't => exact ⟨_, .refl, .inr ⟨_, _, rfl⟩⟩
    case join r rs =>
      have ⟨_, rs, h⟩ := ih ⟨rs, nfn⟩ nfn rfl
      exact ⟨_, .trans r rs, h⟩

theorem join_inv {m₁ m₂ n} (r : .join m₁ m₂ ⇓ₙ n) :
  m₂ ⇒⋆ n ∨ (∃ v, m₂ ⇒⋆ jump 0 v ∧ m₁⦃v⦄ ⇒⋆ n) ∨
  (∃ j v, m₂ ⇒⋆ jump (j + 1) v ∧ renameJCom succ n = jump (j + 1) v) := by
  let ⟨rn, nfn⟩ := r
  match join_inv' r with
  | ⟨n', rm₂, .inl nfn⟩ =>
    have rm₂' := Evals.join (m := m₁) rm₂
    cases n' <;> cases nfn
    all_goals
      have rn' := RTC.trans' rm₂' (.once (by constructor))
      let ⟨_, r₁, r₂⟩ := confluence rn rn'
      rw [← nfn.steps r₁] at r₂
    case ret => rw [r₂.ret_inv] at rm₂; exact .inl rm₂
    case lam => rw [r₂.lam_inv] at rm₂; exact .inl rm₂
    case prod => rw [r₂.prod_inv] at rm₂; exact .inl rm₂
  | ⟨_, rm₂, .inr ⟨_, _, e⟩⟩ =>
    subst e
    have rn' := Evals.join (m := m₁) rm₂
    let ⟨_, r₁, r₂⟩ := confluence rn rn'
    rw [← nfn.steps r₁] at r₂
    cases r₂
    case refl => cases nfn
    case trans rj rn =>
      cases rj
      case join r => cases r
      case γ => exact .inr (.inl ⟨_, rm₂, rn⟩)
      case join't =>
        rw [← Evals.jump_inv rn]
        exact .inr (.inr ⟨_, _, rm₂, rfl⟩)

end Norm

/-*---------------------
  Strong normalization
---------------------*-/

inductive SN : Com → Prop where
  | sn : ∀ m, (∀ n, m ⇒ n → SN n) → SN m

theorem SN.nf {m} (nfm : nf m) : SN m := by
  constructor; intro n r; cases nfm.stepn't r

theorem Evals.sn {m n} (r : m ⇒⋆ n) (nfn : nf n) : SN m := by
  induction r
  case refl => exact .nf nfn
  case trans r _ ih => constructor; intro _ r'; rw [← Eval.det r r']; exact ih nfn
