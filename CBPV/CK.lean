import CBPV.RTC
import CBPV.Syntax
import CBPV.Evaluation

open Val Com

namespace CK

inductive F : Type where
  | app : Val → F
  | letin : Com → F
  | fst : F
  | snd : F
  | join : String → Com → F
open F

def K := List F
def CK := Com × K

@[simp]
def renameK (ξ : Nat → Nat) : K → K
  | [] => []
  | .app v :: k => app (renameVal ξ v) :: renameK ξ k
  | .letin m :: k => letin (renameCom (lift ξ) m) :: renameK ξ k
  | .fst :: k => fst :: renameK ξ k
  | .snd :: k => snd :: renameK ξ k
  | .join j m :: k => join j (renameCom ξ m) :: renameK ξ k

@[simp]
def dismantle (n : Com) : K → Com
  | [] => n
  | .app v :: k => dismantle (app n v) k
  | .letin m :: k => dismantle (letin n m) k
  | .fst :: k => dismantle (fst n) k
  | .snd :: k => dismantle (snd n) k
  | .join j m :: k => dismantle (join j m n) k

section
set_option hygiene false
local infix:40 "⤳" => Step
inductive Step : CK → CK → Prop where
  -- reduction steps
  | β {m v k} :          ⟨lam m, app v :: k⟩         ⤳ ⟨m⦃v⦄, k⟩
  | ζ {v m k} :          ⟨ret v, letin m :: k⟩       ⤳ ⟨m⦃v⦄, k⟩
  | ιl {v m n k} :       ⟨case (inl v) m n, k⟩       ⤳ ⟨m⦃v⦄, k⟩
  | ιr {v m n k} :       ⟨case (inr v) m n, k⟩       ⤳ ⟨n⦃v⦄, k⟩
  | π {m k} :            ⟨force (thunk m), k⟩        ⤳ ⟨m, k⟩
  | π1 {m n k} :         ⟨prod m n, fst :: k⟩        ⤳ ⟨m, k⟩
  | π2 {m n k} :         ⟨prod m n, snd :: k⟩        ⤳ ⟨n, k⟩
  | γ {j m v k} :        ⟨jump j v, join j m :: k⟩   ⤳ ⟨m⦃v⦄, k⟩
  -- congruence rules
  | app {m v k} :        ⟨app m v, k⟩                ⤳ ⟨m, app v :: k⟩
  | letin {m n k} :      ⟨letin m n, k⟩              ⤳ ⟨m, letin n :: k⟩
  | fst {m k} :          ⟨fst m, k⟩                  ⤳ ⟨m, fst :: k⟩
  | snd {m k} :          ⟨snd m, k⟩                  ⤳ ⟨m, snd :: k⟩
  | join {j m n k} :     ⟨join j m n, k⟩             ⤳ ⟨n, join j m :: k⟩
  -- drop joins
  | ret {j m v k} :      ⟨ret v, join j m :: k⟩      ⤳ ⟨ret v, k⟩
  | lam {j m n k} :      ⟨lam n, join j m :: k⟩      ⤳ ⟨lam n, k⟩
  | prod {j m n₁ n₂ k} : ⟨prod n₁ n₂, join j m :: k⟩ ⤳ ⟨prod n₁ n₂, k⟩
  -- drop jump frames
  | join't {j j' m v k} : j ≠ j' →
                         ⟨jump j v, join j' m :: k⟩  ⤳ ⟨jump j v, k⟩
  | appn't {j v w k} :   ⟨jump j v, app w :: k⟩      ⤳ ⟨jump j v, k⟩
  | letn't {j m v k} :   ⟨jump j v, letin m :: k⟩    ⤳ ⟨jump j v, k⟩
  | fstn't {j v k} :     ⟨jump j v, fst :: k⟩        ⤳ ⟨jump j v, k⟩
  | sndn't {j v k} :     ⟨jump j v, snd :: k⟩        ⤳ ⟨jump j v, k⟩
end
infix:40 "⤳" => Step

@[reducible] def Steps := RTC Step
infix:40 "⤳⋆"  => Steps

end CK

namespace Big

section
set_option hygiene false
local infix:40 "⇓" => BStep
inductive BStep : Com → Com → Prop where
  -- terminals
  | ret {v} : ret v ⇓ ret v
  | lam {m} : lam m ⇓ lam m
  | prod {m₁ m₂} : prod m₁ m₂ ⇓ prod m₁ m₂
  | jump {j v} : jump j v ⇓ jump j v
  -- eliminators
  | π {m t} :
    m ⇓ t →
    -------------------
    force (thunk m) ⇓ t
  | β {n t m} {v : Val} :
    n ⇓ lam m →
    m⦃v⦄ ⇓ t →
    ---------------------------
    app n v ⇓ t
  | ζ {n t v m} :
    n ⇓ ret v →
    m⦃v⦄ ⇓ t →
    ---------------------------
    letin n m ⇓ t
  | ιl {m₁ m₂ t} {v : Val}:
    m₁⦃v⦄ ⇓ t →
    ----------------------------
    case (inl v) m₁ m₂ ⇓ t
  | ιr {m₁ m₂ t} {v : Val}:
    m₂⦃v⦄ ⇓ t →
    ----------------------------
    case (inr v) m₁ m₂ ⇓ t
  | π1 {n t m₁ m₂} :
    n ⇓ prod m₁ m₂ →
    m₁ ⇓ t →
    ----------------
    fst n ⇓ t
  | π2 {n t m₁ m₂} :
    n ⇓ prod m₁ m₂ →
    m₂ ⇓ t →
    ----------------
    snd n ⇓ t
  | γ {j m n v t} :
    n ⇓ jump j v →
    m⦃v⦄ ⇓ t →
    --------------
    join j m n ⇓ t
  -- drop joins
  | joinret {j m n v} :
    n ⇓ ret v →
    ------------------
    join j m n ⇓ ret v
  | joinlam {j m n n'} :
    n ⇓ lam n' →
    -------------------
    join j m n ⇓ lam n'
  | joinprod {j m n n₁ n₂} :
    n ⇓ prod n₁ n₂ →
    -----------------------
    join j m n ⇓ prod n₁ n₂
  -- drop jumps
  | join't {j j' m n v} : j ≠ j' →
    n ⇓ jump j v →
    ----------------------
    join j' m n ⇓ jump j v
  | appn't {j n v w} :
    n ⇓ jump j v →
    ------------------
    app n w ⇓ jump j v
  | letn't {j n m v} :
    n ⇓ jump j v →
    --------------------
    letin n m ⇓ jump j v
  | fstn't {j n v} :
    n ⇓ jump j v →
    ----------------
    fst n ⇓ jump j v
  | sndn't {j n v} :
    n ⇓ jump j v →
    ----------------
    snd n ⇓ jump j v
end
infix:40 "⇓" => BStep

theorem BStep.terminal {n} (nfn : nf n) : n ⇓ n := by
  mutual_induction n generalizing nfn
  all_goals simp at nfn <;> constructor

theorem BStep.determinism {m t₁ t₂} (r₁ : m ⇓ t₁) (r₂ : m ⇓ t₂) : t₁ = t₂ := by
  induction r₁ generalizing t₂ <;> cases r₂
  case β.β ih₁ ih₂ _ h₁ h₂
    | ζ.ζ ih₁ ih₂ _ h₁ h₂ =>
    injection ih₁ h₁ with e; subst e; exact ih₂ h₂
  case π1.π1 ih₁ ih₂ _ _ h₁ h₂
    | π2.π2 ih₁ ih₂ _ _ h₁ h₂ =>
    injection ih₁ h₁ with e₁ e₂; subst e₁ e₂; exact ih₂ h₂
  case γ.γ ih₁ ih₂ _ h₁ h₂ =>
    injection ih₁ h₁ with _ e; subst e; exact ih₂ h₂
  case β.appn't ih _ _ _ h | appn't.β ih _ h _
    | ζ.letn't ih _ _ _ h | letn't.ζ ih _ h _
    | π1.fstn't ih _ _ _ h | fstn't.π1 ih _ _ h _
    | π2.sndn't ih _ _ _ h | sndn't.π2 ih _ _ h _
    | γ.joinlam ih _ _ h | γ.joinret ih _ _ h | γ.joinprod ih _ _ _ h
    | joinlam.γ ih _ h _ | joinret.γ ih _ h _ | joinprod.γ ih _ h _ => cases ih h
  case γ.join't ih _ _ _ e h | join't.γ e _ ih _ h _ => cases ih h; contradiction
  all_goals apply_rules

theorem BStep.app {m n v t} (h : ∀ t, m ⇓ t → n ⇓ t) : app m v ⇓ t → app n v ⇓ t := by
  intro r; generalize e : Com.app m v = mv at r
  induction r generalizing m n <;> injection e
  case β h₁ h₂ _ _ em ev => subst em ev; exact β (h _ h₁) h₂
  case appn't h₁ _ em ev => subst em ev; exact appn't (h _ h₁)

theorem BStep.letin {n₁ n₂ m t} (h : ∀ t, n₁ ⇓ t → n₂ ⇓ t) : letin n₁ m ⇓ t → letin n₂ m ⇓ t := by
  intro r; generalize e : Com.letin n₁ m = m' at r
  induction r generalizing m <;> injection e
  case ζ h₁ h₂ _ _ en em => subst en em; exact ζ (h _ h₁) h₂
  case letn't h₁ _ en em => subst en em; exact letn't (h _ h₁)

theorem BStep.fst {m n t} (h : ∀ t, m ⇓ t → n ⇓ t) : fst m ⇓ t → fst n ⇓ t := by
  intro r; generalize e : Com.fst m = m' at r
  induction r generalizing m <;> injection e
  case π1 h₁ h₂ _ _ e => subst e; exact π1 (h _ h₁) h₂
  case fstn't h₁ _ e => subst e; exact fstn't (h _ h₁)

theorem BStep.snd {m n t} (h : ∀ t, m ⇓ t → n ⇓ t) : snd m ⇓ t → snd n ⇓ t := by
  intro r; generalize e : Com.snd m = m' at r
  induction r generalizing m <;> injection e
  case π2 h₁ h₂ _ _ e => subst e; exact π2 (h _ h₁) h₂
  case sndn't h₁ _ e => subst e; exact sndn't (h _ h₁)

theorem BStep.join {j m n₁ n₂ t} (h : ∀ t, n₁ ⇓ t → n₂ ⇓ t) : join j m n₁ ⇓ t → join j m n₂ ⇓ t := by
  intro r; generalize e : Com.join j m n₁ = m' at r
  induction r generalizing m <;> injection e
  case γ h₁ h₂ _ _ ej em en => subst ej em en; exact γ (h _ h₁) h₂
  case join't e h₁ _ ej em en => subst ej em en; exact join't e (h _ h₁)
  case joinret h₁ _ ej em en => subst ej em en; exact joinret (h _ h₁)
  case joinlam h₁ _ ej em en => subst ej em en; exact joinlam (h _ h₁)
  case joinprod h₁ _ ej em en => subst ej em en; exact joinprod (h _ h₁)

end Big

namespace Eq

section
set_option hygiene false
local infix:40 "≡" => EqVal
local infix:40 "≡" => EqCom
mutual
inductive EqVal : Val → Val → Prop
  | var {x} : var x ≡ var x
  | unit : unit ≡ unit
  | inl {v w : Val} : v ≡ w → inl v ≡ inl w
  | inr {v w : Val} : v ≡ w → inr v ≡ inr w
  | thunk {m n : Com} : m ≡ n → thunk m ≡ thunk n
  | sym {v w : Val} : w ≡ v → v ≡ w
  | trans {u v w : Val} : u ≡ v → v ≡ w → u ≡ w

inductive EqCom : Com → Com → Prop
  -- congruence rules
  | force {v w : Val} : v ≡ w → force v ≡ force w
  | lam {m n : Com} : m ≡ n → lam m ≡ lam n
  | app {m n : Com} {v w : Val} : m ≡ n → v ≡ w → app m v ≡ app n w
  | ret {v w : Val} : v ≡ w → ret v ≡ ret w
  | letin {n₁ n₂ m₁ m₂ : Com} : m₁ ≡ n₁ → m₂ ≡ n₂ → letin m₁ m₂ ≡ letin n₁ n₂
  | case {v w : Val} {m₁ n₁ m₂ n₂ : Com} : v ≡ w → m₁ ≡ n₁ → m₂ ≡ n₂ → case v m₁ m₂ ≡ case w n₁ n₂
  | prod {m₁ m₂ n₁ n₂ : Com} : m₁ ≡ n₁ → m₂ ≡ n₂ → prod m₁ m₂ ≡ prod n₁ n₂
  | fst {m n : Com} : m ≡ n → fst m ≡ fst n
  | snd {m n : Com} : m ≡ n → snd m ≡ snd n
  | join {j} {m₁ m₂ n₁ n₂ : Com} : m₁ ≡ n₁ → m₂ ≡ n₂ → join j m₁ m₂ ≡ join j n₁ n₂
  | jump {j} {v w : Val} : v ≡ w → jump j v ≡ jump j w
  -- reduction rules
  | β {m v} : app (lam m) v ≡ m⦃v⦄
  | ζ {m v} : letin (ret v) m ≡ m⦃v⦄
  | ιl {v m₁ m₂} : case (inl v) m₁ m₂ ≡ m₁⦃v⦄
  | ιr {v m₁ m₂} : case (inr v) m₁ m₂ ≡ m₂⦃v⦄
  | π {m} : force (thunk m) ≡ m
  | π1 {m₁ m₂} : fst (prod m₁ m₂) ≡ m₁
  | π2 {m₁ m₂} : snd (prod m₁ m₂) ≡ m₂
  | γ {j m v} : join j m (jump j v) ≡ m⦃v⦄
  -- drop joins
  | joinret {j m v} : join j m (ret v) ≡ ret v
  | joinlam {j m n} : join j m (lam n) ≡ lam n
  | joinprod {j m n₁ n₂} : join j m (prod n₁ n₂) ≡ prod n₁ n₂
  -- drop jump contexts
  | join't {j j' m v} : j ≠ j' → join j' m (jump j v) ≡ jump j v
  | appn't {j v w} : app (jump j v) w ≡ jump j v
  | letn't {j m v} : letin (jump j v) m ≡ jump j v
  | fstn't {j v} : fst (jump j v) ≡ jump j v
  | sndn't {j v} : snd (jump j v) ≡ jump j v
  -- partial equivalence
  | sym {m n : Com} : n ≡ m → m ≡ n
  | trans {m n p : Com} : m ≡ n → n ≡ p → m ≡ p
end
end
infix:40 "≡" => EqVal
infix:40 "≡" => EqCom

theorem reflValCom :
  (∀ {v : Val}, v ≡ v) ∧
  (∀ {m : Com}, m ≡ m) := by
  refine ⟨λ {v} ↦ ?val, λ {m} ↦ ?com⟩
  mutual_induction v, m
  all_goals constructor <;> assumption

@[refl] theorem EqVal.refl : ∀ {v : Val}, v ≡ v := reflValCom.left
@[refl] theorem EqCom.refl : ∀ {m : Com}, m ≡ m := reflValCom.right

instance : Trans EqCom EqCom EqCom where
  trans := .trans

end Eq

open CK Big

/-* CK machine semantics is sound wrt small-step evaluation semantics *-/

theorem evalCongK {m n k} (r : m ⇒ n) : dismantle m k ⇒ dismantle n k := by
  induction k generalizing m n
  case nil => simp [r]
  case cons f _ ih =>
    cases f
    all_goals apply ih; constructor; apply r

theorem stepEval {m n k₁ k₂} (r : ⟨m, k₁⟩ ⤳ ⟨n, k₂⟩) :
  (dismantle m k₁ ⇒ dismantle n k₂) ∨ (dismantle m k₁ = dismantle n k₂) := by
  generalize e₁ : (m, k₁) = ck₁ at r
  generalize e₂ : (n, k₂) = ck₂ at r
  induction r generalizing m n k₁ k₂
  all_goals injection e₁ with em ek₁; subst em ek₁
  all_goals injection e₂ with en ek₂; subst en ek₂
  case app | letin | fst | snd | join => right; rfl
  all_goals (try simp); left; apply evalCongK; constructor
  case join't => assumption

theorem stepEvals {m n k₁ k₂} (r : ⟨m, k₁⟩ ⤳⋆ ⟨n, k₂⟩) : dismantle m k₁ ⇒⋆ dismantle n k₂ := by
  generalize e₁ : (m, k₁) = ck₁ at r
  generalize e₂ : (n, k₂) = ck₂ at r
  induction r generalizing m n k₁ k₂
  case refl => subst e₁; injection e₂ with em ek; subst em ek; rfl
  case trans ck _ r _ ih =>
    subst e₁ e₂; cases ck; specialize ih rfl rfl
    match stepEval r with
    | .inl r => exact .trans r ih
    | .inr e => simp [e, ih]

theorem stepEvalsNil {m n} : ⟨m, []⟩ ⤳⋆ ⟨n, []⟩ → m ⇒⋆ n := stepEvals

/-* CK machine semantics is sound wrt big-step semantics *-/

theorem bigCongK {m n t k} (h : ∀ t, n ⇓ t → m ⇓ t) : dismantle n k ⇓ t → dismantle m k ⇓ t := by
  induction k generalizing m n
  case nil => exact h _
  case cons f _ ih =>
    cases f <;> refine ih (λ t ↦ ?_)
    all_goals apply_assumption [BStep.app h, BStep.letin h, BStep.fst h, BStep.snd h, BStep.join h]

theorem bigStep {m n t k₁ k₂} (r : ⟨m, k₁⟩ ⤳ ⟨n, k₂⟩) : dismantle n k₂ ⇓ t → dismantle m k₁ ⇓ t := by
  generalize em : (m, k₁) = mk at r
  generalize en : (n, k₂) = nk at r
  induction r generalizing m n k₁ k₂
  all_goals injection em with em ek; subst em ek
  all_goals injection en with en ek; subst en ek
  all_goals apply bigCongK; (try simp) <;> intro t r
  case β | ζ | π1 | π2 | γ => constructor; constructor; assumption
  case ιl | ιr | π => constructor; assumption
  all_goals cases r
  case ret => exact .joinret .ret
  case lam => exact .joinlam .lam
  case prod => exact .joinprod .prod
  case join't e => exact .join't e .jump
  case appn't => exact .appn't .jump
  case letn't => exact .letn't .jump
  case fstn't => exact .fstn't .jump
  case sndn't => exact .sndn't .jump

theorem bigSteps {m n t k₁ k₂} (r : ⟨m, k₁⟩ ⤳⋆ ⟨n, k₂⟩) : dismantle n k₂ ⇓ t → dismantle m k₁ ⇓ t := by
  generalize em : (m, k₁) = mk at r
  generalize en : (n, k₂) = nk at r
  induction r generalizing m n k₁ k₂ <;> intro rn
  case refl => subst en; injection em with em ek; subst em ek; exact rn
  case trans rm _ ih => subst en em; exact bigStep rm (ih rfl rfl rn)

theorem bigStepsNil {m t} (nfn : nf t)  (r : ⟨m, []⟩ ⤳⋆ ⟨t, []⟩) : m ⇓ t :=
  bigSteps r (.terminal nfn)

/-* CK machine semantics is complete wrt big-step semantics *-/

theorem stepBig {m n k} (r : m ⇓ n) : ⟨m, k⟩ ⤳⋆ ⟨n, k⟩ := by
  induction r generalizing k
  case lam | ret | prod | jump => rfl
  case π ih => exact .trans .π ih
  case ιl ih => exact .trans .ιl ih
  case ιr ih => exact .trans .ιr ih
  case β n t m v _ _ ih₁ ih₂ =>
    calc ⟨app n v, k⟩
      _ ⤳  ⟨n, .app v :: k⟩     := .app
      _ ⤳⋆ ⟨lam m, .app v :: k⟩ := ih₁
      _ ⤳  ⟨m⦃v⦄, k⟩            := .β
      _ ⤳⋆ ⟨t, k⟩               := ih₂
  case ζ n t v m _ _ ih₁ ih₂ =>
    calc ⟨letin n m, k⟩
      _ ⤳  ⟨n, .letin m :: k⟩     := .letin
      _ ⤳⋆ ⟨ret v, .letin m :: k⟩ := ih₁
      _ ⤳  ⟨m⦃v⦄, k⟩              := .ζ
      _ ⤳⋆ ⟨t, k⟩                 := ih₂
  case π1 n t m₁ m₂ _ _ ih₁ ih₂ =>
    calc ⟨fst n, k⟩
      _ ⤳  ⟨n, .fst :: k⟩          := .fst
      _ ⤳⋆ ⟨prod m₁ m₂, .fst :: k⟩ := ih₁
      _ ⤳  ⟨m₁, k⟩                 := .π1
      _ ⤳⋆ ⟨t, k⟩                  := ih₂
  case π2 n t m₁ m₂ _ _ ih₁ ih₂ =>
    calc ⟨snd n, k⟩
      _ ⤳  ⟨n, .snd :: k⟩          := .snd
      _ ⤳⋆ ⟨prod m₁ m₂, .snd :: k⟩ := ih₁
      _ ⤳  ⟨m₂, k⟩                 := .π2
      _ ⤳⋆ ⟨t, k⟩                  := ih₂
  case γ j m n v t _ _ ih₁ ih₂ =>
    calc ⟨join j m n, k⟩
      _ ⤳  ⟨n, .join j m :: k⟩        := .join
      _ ⤳⋆ ⟨jump j v, .join j m :: k⟩ := ih₁
      _ ⤳  ⟨m⦃v⦄, k⟩                  := .γ
      _ ⤳⋆ ⟨t, k⟩                     := ih₂
  case joinret ih => exact .trans' (.trans .join ih) (.once .ret)
  case joinlam ih => exact .trans' (.trans .join ih) (.once .lam)
  case joinprod ih => exact .trans' (.trans .join ih) (.once .prod)
  case join't e _ ih =>  exact .trans' (.trans .join ih) (.once (.join't e))
  case appn't ih => exact .trans' (.trans .app ih) (.once .appn't)
  case letn't ih => exact .trans' (.trans .letin ih) (.once .letn't)
  case fstn't ih => exact .trans' (.trans .fst ih) (.once .fstn't)
  case sndn't ih => exact .trans' (.trans .snd ih) (.once .sndn't)

/-* CK machine is complete wrt small-step evaluation via big-step *-/

theorem evalBig {m n t} (r : m ⇒ n) : n ⇓ t → m ⇓ t := by
  induction r generalizing t <;> intro r
  case π => exact .π r
  case β => exact .β .lam r
  case ζ => exact .ζ .ret r
  case ιl => exact .ιl r
  case ιr => exact .ιr r
  case π1 => exact .π1 .prod r
  case π2 => exact .π2 .prod r
  case γ => exact .γ .jump r
  case app ih =>
    cases r
    case β r₁ r₂ => exact .β (ih r₁) r₂
    case appn't r => exact .appn't (ih r)
  case letin ih =>
    cases r
    case ζ r₁ r₂ => exact .ζ (ih r₁) r₂
    case letn't r => exact .letn't (ih r)
  case fst ih =>
    cases r
    case π1 r₁ r₂ => exact .π1 (ih r₁) r₂
    case fstn't r => exact .fstn't (ih r)
  case snd ih =>
    cases r
    case π2 r₁ r₂ => exact .π2 (ih r₁) r₂
    case sndn't r => exact .sndn't (ih r)
  case join ih =>
    cases r
    case γ r₁ r₂ => exact .γ (ih r₁) r₂
    case joinret r => exact .joinret (ih r)
    case joinlam r => exact .joinlam (ih r)
    case joinprod r => exact .joinprod (ih r)
    case join't e r => exact .join't e (ih r)
  case ret => cases r; exact .joinret .ret
  case lam => cases r; exact .joinlam .lam
  case prod => cases r; exact .joinprod .prod
  case join't e => cases r; exact .join't e .jump
  case appn't => cases r; exact .appn't .jump
  case letn't => cases r; exact .letn't .jump
  case fstn't => cases r; exact .fstn't .jump
  case sndn't => cases r; exact .sndn't .jump

theorem evalBigs {m n t} (r : m ⇒⋆ n) : n ⇓ t → m ⇓ t := by
  induction r generalizing t <;> intro r
  case refl => exact r
  case trans r' _ ih => exact evalBig r' (ih r)

theorem bigNf {t} (nt : nf t) : t ⇓ t := by
  mutual_induction t generalizing nt
  all_goals simp at nt
  all_goals constructor

theorem evalStep {m t} (nt : nf t) (r : m ⇒⋆ t) : ⟨m, []⟩ ⤳⋆ ⟨t, []⟩ :=
  stepBig (evalBigs r (bigNf nt))

/-* CK machine is sound wrt equational theory *-/

theorem eqCongK {m n : Com} {k} (e : m ≡ n) : dismantle m k ≡ dismantle n k := by
  induction k generalizing m n
  case nil => simp [e]
  case cons f _ ih =>
    cases f <;> (apply ih; constructor)
    all_goals first | assumption | rfl

theorem stepEq {m n k₁ k₂} (r : ⟨m, k₁⟩ ⤳ ⟨n, k₂⟩) : dismantle m k₁ ≡ dismantle n k₂ := by
  cases r
  case app | letin | fst | snd | join => rfl
  all_goals (try simp); apply eqCongK; constructor
  case join't => assumption

theorem stepsEq {m n k₁ k₂} (r : ⟨m, k₁⟩ ⤳⋆ ⟨n, k₂⟩) : dismantle m k₁ ≡ dismantle n k₂ := by
  generalize e₁ : (m, k₁) = ck₁ at r
  generalize e₂ : (n, k₂) = ck₂ at r
  induction r generalizing m n k₁ k₂
  case refl => subst e₁; injection e₂ with em ek; subst em ek; rfl
  case trans ck _ r _ ih => subst e₁ e₂; exact .trans (stepEq r) (ih rfl rfl)

theorem stepsEqNil {m n} (r : ⟨m, []⟩ ⤳⋆ ⟨n, []⟩) : m ≡ n := stepsEq r
