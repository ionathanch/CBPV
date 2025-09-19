import CBPV.RTC
import CBPV.Syntax
import CBPV.Evaluation

open Val Com

namespace CK

inductive F : Nat → Type where
  | app : Val → F 0
  | letin {δ} : Com δ → F δ
  | fst : F 0
  | snd : F 0
  | join {δ} : Com δ → F (δ + 1)
open F

inductive K : Nat → Type where
  | nil : K 0
  | app {δ} : Val → K δ → K 0
  | letin {δ} : Com δ → K δ → K 0
  | fst {δ} : K δ → K 0
  | snd {δ} : K δ → K 0
  | join {δ} : Com δ → K δ → K (δ + 1)

def CK := Σ δ, Com δ × K δ

@[simp]
def K.renameK {δ} (ξ : Nat → Nat) : K δ → K δ
  | nil => nil
  | app v k => app (renameVal ξ v) (renameK ξ k)
  | letin m k => letin (renameCom (lift ξ) m) (renameK ξ k)
  | fst k => fst (renameK ξ k)
  | snd k => snd (renameK ξ k)
  | join m k => join (renameCom ξ m) (renameK ξ k)

@[simp]
def dismantle {δ} (n : Com δ) : K δ → Com 0
  | .nil => n
  | .app v k => dismantle (app n v) k
  | .letin m k => dismantle (letin n m) k
  | .fst k => dismantle (fst n) k
  | .snd k => dismantle (snd n) k
  | .join m k => dismantle (join m n) k

section
set_option hygiene false
local infix:40 "⤳" => Step
inductive Step : CK → CK → Prop where
  -- reduction steps
  | β {δ m v k} :        ⟨0, lam m, .app v k⟩              ⤳ ⟨δ, weakenJCom δ m⦃v⦄, k⟩
  | ζ {δ v m k} :        ⟨0, ret v, .letin m k⟩            ⤳ ⟨δ, m⦃v⦄, k⟩
  | ιl {δ v m n k} :     ⟨δ, case (inl v) m n, k⟩          ⤳ ⟨δ, m⦃v⦄, k⟩
  | ιr {δ v m n k} :     ⟨δ, case (inr v) m n, k⟩          ⤳ ⟨δ, n⦃v⦄, k⟩
  | π {δ m k} :          ⟨δ, force (thunk m), k⟩           ⤳ ⟨δ, weakenJCom δ m, k⟩
  | π1 {δ m n k} :       ⟨0, prod m n, .fst k⟩             ⤳ ⟨δ, weakenJCom δ m, k⟩
  | π2 {δ m n k} :       ⟨0, prod m n, .snd k⟩             ⤳ ⟨δ, weakenJCom δ n, k⟩
  | γ {δ m v k} :        ⟨δ + 1, jump 0 v, .join m k⟩      ⤳ ⟨δ, m⦃v⦄, k⟩
  -- congruence rules
  | app {δ m v k} :      ⟨δ, app m v, k⟩                   ⤳ ⟨0, m, .app v k⟩
  | letin {δ m n k} :    ⟨δ, letin m n, k⟩                 ⤳ ⟨0, m, .letin n k⟩
  | fst {δ m k} :        ⟨δ, fst m, k⟩                     ⤳ ⟨0, m, .fst k⟩
  | snd {δ m k} :        ⟨δ, snd m, k⟩                     ⤳ ⟨0, m, .snd k⟩
  | join {δ m n k} :     ⟨δ, join m n, k⟩                  ⤳ ⟨δ + 1, n, .join m k⟩
  -- drop joins
  | ret {δ m v k} :      ⟨δ + 1, ret v, .join m k⟩         ⤳ ⟨δ, ret v, k⟩
  | lam {δ m n k} :      ⟨δ + 1, lam n, .join m k⟩         ⤳ ⟨δ, lam n, k⟩
  | prod {δ m n₁ n₂ k} : ⟨δ + 1, prod n₁ n₂, .join m k⟩    ⤳ ⟨δ, prod n₁ n₂, k⟩
  | join't {δ j m v k} : ⟨δ + 1, jump j.succ v, .join m k⟩ ⤳ ⟨δ, jump j v, k⟩
end
infix:40 "⤳" => Step

@[reducible] def Steps := RTC Step
infix:40 "⤳⋆"  => Steps

end CK

open CK

section
set_option hygiene false
local infix:40 "⇓" => Big
inductive Big : ∀ {δ}, Com δ → Com δ → Prop where
  -- terminals
  | ret {v} : ret v ⇓ ret v
  | lam {m} : lam m ⇓ lam m
  | prod {m₁ m₂} : prod m₁ m₂ ⇓ prod m₁ m₂
  | jump {j v} : jump j v ⇓ jump j v
  -- eliminators
  | π {δ m t} :
    weakenJCom δ m ⇓ t →
    --------------------
    force (thunk m) ⇓ t
  | β {δ n t m} {v : Val} :
    n ⇓ lam m →
    weakenJCom δ m⦃v⦄ ⇓ t →
    -----------------------
    app n v ⇓ t
  | ζ {n t v m} :
    n ⇓ ret v →
    m⦃v⦄ ⇓ t →
    -------------
    letin n m ⇓ t
  | ιl {m₁ m₂ t} {v : Val}:
    m₁⦃v⦄ ⇓ t →
    ----------------------
    case (inl v) m₁ m₂ ⇓ t
  | ιr {m₁ m₂ t} {v : Val}:
    m₂⦃v⦄ ⇓ t →
    ----------------------
    case (inr v) m₁ m₂ ⇓ t
  | π1 {δ n t m₁ m₂} :
    n ⇓ prod m₁ m₂ →
    weakenJCom δ m₁ ⇓ t →
    ---------------------
    fst n ⇓ t
  | π2 {δ n t m₁ m₂} :
    n ⇓ prod m₁ m₂ →
    weakenJCom δ m₂ ⇓ t →
    ---------------------
    snd n ⇓ t
  | γ {m n v t} :
    n ⇓ jump 0 v →
    m⦃v⦄ ⇓ t →
    ------------
    join m n ⇓ t
  -- drop joins
  | joinret {m n v} :
    n ⇓ ret v →
    ----------------
    join m n ⇓ ret v
  | joinlam {m n n'} :
    n ⇓ lam n' →
    -----------------
    join m n ⇓ lam n'
  | joinprod {m n n₁ n₂} :
    n ⇓ prod n₁ n₂ →
    ---------------------
    join m n ⇓ prod n₁ n₂
  | join't {j m n v} :
    n ⇓ jump j.succ v →
    -------------------
    join m n ⇓ jump j v
end
infix:40 "⇓" => Big

namespace Big

theorem terminal {δ} {n : Com δ} (nfn : nf n) : n ⇓ n := by
  mutual_induction n generalizing nfn
  all_goals simp at nfn <;> constructor

theorem determinism {δ} {m t₁ t₂ : Com δ} (r₁ : m ⇓ t₁) (r₂ : m ⇓ t₂) : t₁ = t₂ := by
  induction r₁ <;> cases r₂
  case β.β ih₁ ih₂ _ h₁ h₂
    | ζ.ζ ih₁ ih₂ _ h₁ h₂
    | π1.π1 ih₁ ih₂ _ _ h₁ h₂
    | π2.π2 ih₁ ih₂ _ _ h₁ h₂
    | γ.γ ih₁ ih₂ _ h₁ h₂
    | joinret.joinret ih₁ _ h₁
    | joinlam.joinlam ih₁ _ h₁
    | joinprod.joinprod ih₁ _ _ h₁ =>
    injection ih₁ h₁; subst_vars; first | rfl | simp [ih₂ h₂]
  case γ.joinlam ih _ _ h | γ.joinret ih _ _ h | γ.joinprod ih _ _ _ h
    | joinlam.γ ih _ h _ | joinret.γ ih _ h _ | joinprod.γ ih _ h _
    | γ.join't ih _ _ e h | join't.γ e _ ih _ h _
    | joinret.join't ih _ _ h | join't.joinret ih _ h
    | joinprod.join't ih _ _ h | join't.joinprod ih _ _ h
    | joinlam.join't ih _ _ h | join't.joinlam ih _ h
    | joinret.joinlam ih _ h | joinret.joinprod ih _ _ h
    | joinlam.joinret ih _ h | joinlam.joinprod ih _ _ h
    | joinprod.joinret ih _ h | joinprod.joinlam ih _ h => cases ih h
  case join't.join't ih _ _ h =>
    injection ih h with _ ej ev; rw [Fin.succ_inj.mp ej]; simp [ev]
  all_goals apply_rules

end Big

section
set_option hygiene false
local notation:40 m:41 "≡" n:41 => EqVal m n
local notation:40 m:41 "≡" n:41 => EqCom m n
mutual
inductive EqVal : Val → Val → Prop
  | var {x} : var x ≡ var x
  | unit : unit ≡ unit
  | inl {v w : Val} : v ≡ w → inl v ≡ inl w
  | inr {v w : Val} : v ≡ w → inr v ≡ inr w
  | thunk {m n : Com 0} : m ≡ n → thunk m ≡ thunk n
  | sym {v w : Val} : w ≡ v → v ≡ w
  | trans {u v w : Val} : u ≡ v → v ≡ w → u ≡ w

inductive EqCom : ∀ {δ}, Com δ → Com δ → Prop
  -- congruence rules
  | force {v w : Val} : v ≡ w → force v ≡ force w
  | lam {m n : Com 0} : m ≡ n → lam m ≡ lam n
  | app {m n : Com 0} {v w : Val} : m ≡ n → v ≡ w → app m v ≡ app n w
  | ret {v w : Val} : v ≡ w → ret v ≡ ret w
  | letin {δ} {m₁ n₁ : Com 0} {m₂ n₂ : Com δ} : m₁ ≡ n₁ → m₂ ≡ n₂ → letin m₁ m₂ ≡ letin n₁ n₂
  | case {δ} {v w : Val} {m₁ n₁ m₂ n₂ : Com δ} : v ≡ w → m₁ ≡ n₁ → m₂ ≡ n₂ → case v m₁ m₂ ≡ case w n₁ n₂
  | prod {m₁ m₂ n₁ n₂ : Com 0} : m₁ ≡ n₁ → m₂ ≡ n₂ → prod m₁ m₂ ≡ prod n₁ n₂
  | fst {m n : Com 0} : m ≡ n → fst m ≡ fst n
  | snd {m n : Com 0} : m ≡ n → snd m ≡ snd n
  | join {δ} {m₁ n₁ : Com δ} {m₂ n₂ : Com (δ + 1)} : m₁ ≡ n₁ → m₂ ≡ n₂ → join m₁ m₂ ≡ join n₁ n₂
  | jump {j} {v w : Val} : v ≡ w → jump j v ≡ jump j w
  -- reduction rules
  | β {δ m v} : app (lam m) v ≡ weakenJCom δ m⦃v⦄
  | ζ {m v} : letin (ret v) m ≡ m⦃v⦄
  | ιl {v m₁ m₂} : case (inl v) m₁ m₂ ≡ m₁⦃v⦄
  | ιr {v m₁ m₂} : case (inr v) m₁ m₂ ≡ m₂⦃v⦄
  | π {δ m} : force (thunk m) ≡ weakenJCom δ m
  | π1 {δ m₁ m₂} : fst (prod m₁ m₂) ≡ weakenJCom δ m₁
  | π2 {δ m₁ m₂} : snd (prod m₁ m₂) ≡ weakenJCom δ m₂
  | γ {m v} : join m (jump 0 v) ≡ m⦃v⦄
  -- drop joins
  | joinret {m v} : join m (ret v) ≡ ret v
  | joinlam {m n} : join m (lam n) ≡ lam n
  | joinprod {m n₁ n₂} : join m (prod n₁ n₂) ≡ prod n₁ n₂
  | join't {j m v} : join m (jump j.succ v) ≡ jump j v
  -- partial equivalence
  | sym {δ} {m n : Com δ} : n ≡ m → m ≡ n
  | trans {δ} {m n p : Com δ} : m ≡ n → n ≡ p → m ≡ p
end
end
notation:40 m:41 "≡" n:41 => EqVal m n
notation:40 m:41 "≡" n:41 => EqCom m n

theorem reflValCom :
  (∀ {v : Val}, v ≡ v) ∧
  (∀ {δ} {m : Com δ}, m ≡ m) := by
  refine ⟨λ {v} ↦ ?val, λ {δ m} ↦ ?com⟩
  mutual_induction v, m
  all_goals constructor <;> assumption

@[refl] theorem EqVal.refl : ∀ {v : Val}, v ≡ v := reflValCom.left
@[refl] theorem EqCom.refl : ∀ {δ} {m : Com δ}, m ≡ m := reflValCom.right

instance {δ} : Trans (@EqCom δ) (@EqCom δ) (@EqCom δ) where
  trans := .trans

/-* CK machine semantics is sound wrt small-step evaluation semantics *-/

theorem evalCongK {δ m n} {k : K δ} (r : m ⇒ n) : dismantle m k ⇒ dismantle n k := by
  induction k
  case nil => simp [r]
  all_goals rename_i ih; apply ih; constructor; apply r

theorem stepEval {δ₁ δ₂ m n k₁ k₂} (r : ⟨δ₁, m, k₁⟩ ⤳ ⟨δ₂, n, k₂⟩) :
  (dismantle m k₁ ⇒ dismantle n k₂) ∨ (dismantle m k₁ = dismantle n k₂) := by
  generalize e₁ : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₁ (m, k₁) = ck₁ at r
  generalize e₂ : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₂ (n, k₂) = ck₂ at r
  induction r generalizing m n k₁ k₂
  all_goals injection e₁ with eδ e₁; subst eδ
  all_goals injection e₂ with eδ e₂; subst eδ
  all_goals injection e₁ with em ek₁; subst em ek₁
  all_goals injection e₂ with en ek₂; subst en ek₂
  case app | letin | fst | snd | join => right; rfl
  all_goals (try simp); left; apply evalCongK; (try constructor)
  case β => rw [weakenJSubst]; constructor

theorem stepEvals {δ₁ δ₂ m n k₁ k₂} (r : ⟨δ₁, m, k₁⟩ ⤳⋆ ⟨δ₂, n, k₂⟩) : dismantle m k₁ ⇒⋆ dismantle n k₂ := by
  generalize e₁ : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₁ (m, k₁) = ck₁ at r
  generalize e₂ : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₂ (n, k₂) = ck₂ at r
  induction r generalizing δ₁ δ₂ m n k₁ k₂
  case refl =>
    subst e₁; injection e₂ with eδ emk
    subst eδ; injection emk with em ek
    subst em ek; rfl
  case trans ck _ r _ ih =>
    subst e₁ e₂; cases ck; specialize ih rfl rfl
    match stepEval r with
    | .inl r => exact .trans r ih
    | .inr e => simp [e, ih]

theorem stepEvalsNil {m n} : ⟨0, m, .nil⟩ ⤳⋆ ⟨0, n, .nil⟩ → m ⇒⋆ n := stepEvals

/-* CK machine semantics is sound wrt big-step semantics *-/

theorem bigCongK {δ m n t} {k : K δ} (h : ∀ t, n ⇓ t → m ⇓ t) : dismantle n k ⇓ t → dismantle m k ⇓ t := by
  induction k
  case nil => exact h _
  all_goals rename_i ih; refine ih (λ t r ↦ ?_)
  case join => exact join h r
  all_goals cases r; constructor <;> apply_rules [h]
  where join {δ n₁ n₂} {m t : Com δ} (h : ∀ t, n₁ ⇓ t → n₂ ⇓ t) : join m n₁ ⇓ t → join m n₂ ⇓ t
    | .γ h₁ h₂ => .γ (h _ h₁) h₂
    | .join't h₁ => .join't (h _ h₁)
    | .joinret h₁ => .joinret (h _ h₁)
    | .joinlam h₁ => .joinlam (h _ h₁)
    | .joinprod h₁ => .joinprod (h _ h₁)

theorem bigStep {δ₁ δ₂ m n t k₁ k₂} (r : ⟨δ₁, m, k₁⟩ ⤳ ⟨δ₂, n, k₂⟩) : dismantle n k₂ ⇓ t → dismantle m k₁ ⇓ t := by
  generalize em : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₁ (m, k₁) = mk at r
  generalize en : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₂ (n, k₂) = nk at r
  induction r generalizing m n k₁ k₂
  all_goals injection em with eδ em; subst eδ
  all_goals injection en with eδ em; subst eδ
  all_goals injection em with em ek; subst em ek
  all_goals injection em with en ek; subst en ek
  all_goals apply bigCongK; (try simp) <;> intro t r
  case β | π | π1 | π2 => constructor <;> first | constructor | assumption
  case ζ | γ | ιl | ιr => constructor <;> first | constructor | assumption
  all_goals cases r
  case ret => exact .joinret .ret
  case lam => exact .joinlam .lam
  case prod => exact .joinprod .prod
  case join't => exact .join't .jump

theorem bigSteps {δ₁ δ₂ m n t k₁ k₂} (r : ⟨δ₁, m, k₁⟩ ⤳⋆ ⟨δ₂, n, k₂⟩) : dismantle n k₂ ⇓ t → dismantle m k₁ ⇓ t := by
  generalize em : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₁ (m, k₁) = mk at r
  generalize en : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₂ (n, k₂) = nk at r
  induction r generalizing δ₁ δ₂ m n k₁ k₂ <;> intro rn
  case refl =>
    subst en; injection em with eδ em
    subst eδ; injection em with em ek
    subst em ek; exact rn
  case trans nk _ rm _ ih =>
    subst en em; exact bigStep rm (ih rfl rfl rn)

theorem bigStepsNil {m t} (nfn : nf t)  (r : ⟨0, m, .nil⟩ ⤳⋆ ⟨0, t, .nil⟩) : m ⇓ t :=
  bigSteps r (.terminal nfn)

/-* CK machine semantics is complete wrt big-step semantics *-/

theorem stepBig {δ m n k} (r : m ⇓ n) : ⟨δ, m, k⟩ ⤳⋆ ⟨δ, n, k⟩ := by
  induction r
  case lam | ret | prod | jump => rfl
  case π ih => exact .trans .π ih
  case ιl ih => exact .trans .ιl ih
  case ιr ih => exact .trans .ιr ih
  case β δ n t m v _ _ ih₁ ih₂ =>
    calc   ⟨δ, app n v, k⟩
      _ ⤳  ⟨0, n, .app v k⟩          := .app
      _ ⤳⋆ ⟨0, lam m, .app v k⟩      := ih₁
      _ ⤳  ⟨δ, weakenJCom δ m⦃v⦄, k⟩ := .β
      _ ⤳⋆ ⟨δ, t, k⟩                 := ih₂
  case ζ δ n t v m _ _ ih₁ ih₂ =>
    calc   ⟨δ, letin n m, k⟩
      _ ⤳  ⟨0, n, .letin m k⟩     := .letin
      _ ⤳⋆ ⟨0, ret v, .letin m k⟩ := ih₁
      _ ⤳  ⟨δ, m⦃v⦄, k⟩           := .ζ
      _ ⤳⋆ ⟨δ, t, k⟩              := ih₂
  case π1 δ n t m₁ m₂ _ _ ih₁ ih₂ =>
    calc   ⟨δ, fst n, k⟩
      _ ⤳  ⟨0, n, .fst k⟩          := .fst
      _ ⤳⋆ ⟨0, prod m₁ m₂, .fst k⟩ := ih₁
      _ ⤳  ⟨δ, weakenJCom δ m₁, k⟩ := .π1
      _ ⤳⋆ ⟨δ, t, k⟩               := ih₂
  case π2 δ n t m₁ m₂ _ _ ih₁ ih₂ =>
    calc   ⟨δ, snd n, k⟩
      _ ⤳  ⟨0, n, .snd k⟩          := .snd
      _ ⤳⋆ ⟨0, prod m₁ m₂, .snd k⟩ := ih₁
      _ ⤳  ⟨δ, weakenJCom δ m₂, k⟩ := .π2
      _ ⤳⋆ ⟨δ, t, k⟩               := ih₂
  case γ δ m n v t _ _ ih₁ ih₂ =>
    calc   ⟨δ, join m n, k⟩
      _ ⤳  ⟨δ + 1, n, .join m k⟩        := .join
      _ ⤳⋆ ⟨δ + 1, jump 0 v, .join m k⟩ := ih₁
      _ ⤳  ⟨δ, m⦃v⦄, k⟩                 := .γ
      _ ⤳⋆ ⟨δ, t, k⟩                    := ih₂
  case joinret ih => exact .trans' (.trans .join ih) (.once .ret)
  case joinlam ih => exact .trans' (.trans .join ih) (.once .lam)
  case joinprod ih => exact .trans' (.trans .join ih) (.once .prod)
  case join't ih =>  exact .trans' (.trans .join ih) (.once .join't)

/-* CK machine is complete wrt small-step evaluation via big-step *-/

theorem evalBig {δ} {m n t : Com δ} (r : m ⇒ n) : n ⇓ t → m ⇓ t := by
  induction r <;> intro r
  case π => exact .π r
  case β => rw [← weakenJSubst] at r; exact .β .lam r
  case ζ => exact .ζ .ret r
  case ιl => exact .ιl r
  case ιr => exact .ιr r
  case π1 => exact .π1 .prod r
  case π2 => exact .π2 .prod r
  case γ => exact .γ .jump r
  case app ih => cases r with | β r₁ r₂ => exact .β (ih r₁) r₂
  case letin ih => cases r with | ζ r₁ r₂ => exact .ζ (ih r₁) r₂
  case fst ih => cases r with | π1 r₁ r₂ => exact .π1 (ih r₁) r₂
  case snd ih => cases r with | π2 r₁ r₂ => exact .π2 (ih r₁) r₂
  case join ih =>
    cases r
    case γ r₁ r₂ => exact .γ (ih r₁) r₂
    case joinret r => exact .joinret (ih r)
    case joinlam r => exact .joinlam (ih r)
    case joinprod r => exact .joinprod (ih r)
    case join't r => exact .join't (ih r)
  case ret => cases r; exact .joinret .ret
  case lam => cases r; exact .joinlam .lam
  case prod => cases r; exact .joinprod .prod
  case join't => cases r; exact .join't .jump

theorem evalBigs {δ} {m n t : Com δ} (r : m ⇒⋆ n) : n ⇓ t → m ⇓ t := by
  induction r generalizing t <;> intro r
  case refl => exact r
  case trans r' _ ih => exact evalBig r' (ih r)

theorem bigNf {δ t} (nt : @nf δ t) : t ⇓ t := by
  mutual_induction t generalizing nt
  all_goals simp at nt
  all_goals constructor

theorem evalStep {m t} (nt : nf t) (r : m ⇒⋆ t) : ⟨0, m, .nil⟩ ⤳⋆ ⟨0, t, .nil⟩ :=
  stepBig (evalBigs r (bigNf nt))

/-* CK machine is sound wrt equational theory *-/

theorem eqCongK {δ} {m n : Com δ} {k} (e : m ≡ n) : dismantle m k ≡ dismantle n k := by
  induction k
  case nil => simp [e]
  all_goals rename_i ih; (apply ih; constructor)
  all_goals first | assumption | rfl

theorem stepEq {δ₁ δ₂ m n k₁ k₂} (r : ⟨δ₁, m, k₁⟩ ⤳ ⟨δ₂, n, k₂⟩) : dismantle m k₁ ≡ dismantle n k₂ := by
  cases r
  case app | letin | fst | snd | join => rfl
  all_goals (try simp); apply eqCongK; constructor

theorem stepsEq {δ₁ δ₂ m n k₁ k₂} (r : ⟨δ₁, m, k₁⟩ ⤳⋆ ⟨δ₂, n, k₂⟩) : dismantle m k₁ ≡ dismantle n k₂ := by
  generalize e₁ : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₁ (m, k₁) = ck₁ at r
  generalize e₂ : Sigma.mk (β := λ δ ↦ Com δ × K δ) δ₂ (n, k₂) = ck₂ at r
  induction r generalizing δ₁ δ₂ m n k₁ k₂
  case refl =>
    subst e₁; injection e₂ with eδ emk
    subst eδ; injection emk with em ek
    subst em ek; rfl
  case trans ck _ r _ ih => subst e₁ e₂; exact .trans (stepEq r) (ih rfl rfl)

theorem stepsEqNil {m n} (r : ⟨0, m, .nil⟩ ⤳⋆ ⟨0, n, .nil⟩) : m ≡ n := stepsEq r
