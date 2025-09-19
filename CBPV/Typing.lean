import CBPV.Syntax

open Nat ValType ComType Val Com

section
set_option hygiene false
local notation:40 Γ:41 "⊢" v:41 "∶" A:41 => ValWt Γ v A
local notation:40 Γ:41 "∣" Δ:41 "⊢" m:41 "∶" B:41 => ComWt Γ Δ m B

mutual
inductive ValWt : Ctxt → Val → ValType → Prop where
  | var {Γ : Ctxt} {x A} :
    Γ ∋ x ∶ A →
    -------------
    Γ ⊢ var x ∶ A
  | unit {Γ} : Γ ⊢ unit ∶ Unit
  | inl {Γ v} {A₁ A₂ : ValType} :
    Γ ⊢ v ∶ A₁ →
    ---------------------
    Γ ⊢ inl v ∶ Sum A₁ A₂
  | inr {Γ v} {A₁ A₂ : ValType} :
    Γ ⊢ v ∶ A₂ →
    ---------------------
    Γ ⊢ inr v ∶ Sum A₁ A₂
  | thunk {Γ m} {B : ComType} :
    Γ ∣ ⬝ ⊢ m ∶ B →
    -----------------
    Γ ⊢ thunk m ∶ U B

inductive ComWt : ∀ {δ}, Ctxt → Dtxt δ → Com δ → ComType → Prop where
  | force {Γ Δ v B} :
    Γ ⊢ v ∶ U B →
    -------------------
    Γ ∣ Δ ⊢ force v ∶ B
  | lam {Γ Δ m A} {B : ComType} :
    Γ ∷ A ∣ ⬝ ⊢ m ∶ B →
    -----------------------
    Γ ∣ Δ ⊢ lam m ∶ Arr A B
  | app {Γ Δ m v A B} :
    Γ ∣ ⬝ ⊢ m ∶ Arr A B →
    Γ ⊢ v ∶ A →
    -------------------
    Γ ∣ Δ ⊢ app m v ∶ B
  | ret {Γ Δ v} {A : ValType} :
    Γ ⊢ v ∶ A →
    -------------------
    Γ ∣ Δ ⊢ ret v ∶ F A
  | letin {Γ Δ m n A} {B : ComType} :
    Γ ∣ ⬝ ⊢ m ∶ F A →
    Γ ∷ A ∣ Δ ⊢ n ∶ B →
    ---------------------
    Γ ∣ Δ ⊢ letin m n ∶ B
  | case {Γ Δ v m n A₁ A₂} {B : ComType} :
    Γ ⊢ v ∶ Sum A₁ A₂ →
    Γ ∷ A₁ ∣ Δ ⊢ m ∶ B →
    Γ ∷ A₂ ∣ Δ ⊢ n ∶ B →
    ----------------------
    Γ ∣ Δ ⊢ case v m n ∶ B
  | prod {Γ Δ m n} {B₁ B₂: ComType} :
    Γ ∣ ⬝ ⊢ m ∶ B₁ →
    Γ ∣ ⬝ ⊢ n ∶ B₂ →
    -----------------------------
    Γ ∣ Δ ⊢ prod m n ∶ Prod B₁ B₂
  | fst {Γ Δ m} {B₁ B₂ : ComType} :
    Γ ∣ ⬝ ⊢ m ∶ Prod B₁ B₂ →
    ------------------------
    Γ ∣ Δ ⊢ fst m ∶ B₁
  | snd {Γ Δ m} {B₁ B₂ : ComType} :
    Γ ∣ ⬝ ⊢ m ∶ Prod B₁ B₂ →
    ------------------------
    Γ ∣ Δ ⊢ snd m ∶ B₂
  | join {Γ Δ m n A B} :
    Γ ∷ A ∣ Δ ⊢ m ∶ B →
    Γ ∣ Δ ∷ A ↗ B ⊢ n ∶ B →
    -----------------------
    Γ ∣ Δ ⊢ join m n ∶ B
  | jump {Γ Δ j v A B} :
    Δ ∋ j ∶ A ↗ B →
    Γ ⊢ v ∶ A →
    --------------------
    Γ ∣ Δ ⊢ jump j v ∶ B
end
end

notation:40 Γ:41 "⊢" v:41 "∶" A:41 => ValWt Γ v A
notation:40 Γ:41 "∣" Δ:41 "⊢" m:41 "∶" B:41 => ComWt Γ Δ m B

/-*------------------------------
  Renaming and weakening lemmas
------------------------------*-/

theorem wtRename {ξ} {Γ Ξ : Ctxt} (hξ : Ξ ⊢ ξ ∶ Γ) :
  (∀ {v} {A : ValType}, Γ ⊢ v ∶ A → Ξ ⊢ renameVal ξ v ∶ A) ∧
  (∀ {δ} {Δ : Dtxt δ} {m : Com δ} {B : ComType}, Γ ∣ Δ ⊢ m ∶ B → Ξ ∣ Δ ⊢ renameCom ξ m ∶ B) := by
  refine ⟨λ h ↦ ?wtv, λ h ↦ ?wtm⟩
  mutual_induction h, h generalizing ξ Ξ
  all_goals constructor <;> apply_rules [wRenameLift]

theorem wtRenameVal {ξ} {Γ Δ : Ctxt} {v} {A : ValType} :
  Δ ⊢ ξ ∶ Γ → Γ ⊢ v ∶ A → Δ ⊢ renameVal ξ v ∶ A :=
  λ hξ ↦ (wtRename hξ).left

theorem wtRenameCom {ξ} {Γ Ξ : Ctxt} {δ} {Δ : Dtxt δ} {m : Com δ} {B : ComType} :
  Ξ ⊢ ξ ∶ Γ → Γ ∣ Δ ⊢ m ∶ B → Ξ ∣ Δ ⊢ renameCom ξ m ∶ B :=
  λ hξ ↦ (wtRename hξ).right

theorem wtWeakenVal {Γ A₁ A₂} {v : Val} :
  Γ ⊢ v ∶ A₂ → Γ ∷ A₁ ⊢ renameVal succ v ∶ A₂ :=
    wtRenameVal wRenameSucc

theorem wtWeakenCom {Γ δ Δ A B} {m : Com δ} :
  Γ ∣ Δ ⊢ m ∶ B → Γ ∷ A ∣ Δ ⊢ renameCom succ m ∶ B :=
  wtRenameCom wRenameSucc

theorem wtWeakenCom₂ {Γ δ Δ A₁ A₂ B} {m : Com δ} :
  Γ ∷ A₂ ∣ Δ ⊢ m ∶ B → Γ ∷ A₁ ∷ A₂ ∣ Δ ⊢ renameCom (lift succ) m ∶ B :=
  wtRenameCom (wRenameLift wRenameSucc)

/-* Jump renaming and weakening *-/

theorem wtRenameJ {Γ} {δ δ' ξ} {Δ : Dtxt δ} {Φ : Dtxt δ'} {m B} (hξ : Φ ⊢ ξ ∶ Δ)
  (h : Γ ∣ Δ ⊢ m ∶ B) : Γ ∣ Φ ⊢ renameJCom ξ m ∶ B := by
  mutual_induction h generalizing ξ δ' Φ
  all_goals constructor <;> apply_rules [wRenameJLift]

theorem wtWeakenJ {Γ δ Δ A' B' B} {m : Com δ} :
  Γ ∣ Δ ⊢ m ∶ B → Γ ∣ Δ ∷ A' ↗ B' ⊢ renameJCom Fin.succ m ∶ B :=
  wtRenameJ wRenameJSucc

/-*--------------------------------------
  Rearrangement lemmas for commutations
--------------------------------------*-/

theorem wtLetApp {Γ δ} {Δ : Dtxt δ} {n m v A B} (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Arr A B) (hv : Γ ⊢ v ∶ A) :
  Γ ∣ Δ ⊢ letin n (app m (renameVal succ v)) ∶ B := by
  cases hlet with | letin hn hm =>
  exact .letin hn (.app hm (wtWeakenVal hv))

theorem wtLetFst {Γ δ} {Δ : Dtxt δ} {n m B₁ B₂} (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊢ letin n (fst m) ∶ B₁ := by
  cases hlet with | letin hn hm =>
  exact .letin hn (.fst hm)

theorem wtLetSnd {Γ δ} {Δ : Dtxt δ} {n m B₁ B₂} (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊢ letin n (snd m) ∶ B₂ := by
  cases hlet with | letin hn hm =>
  exact .letin hn (.snd hm)

theorem wtCaseApp {Γ δ} {Δ : Dtxt δ} {v m₁ m₂ w A B} (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Arr A B) (hw : Γ ⊢ w ∶ A) :
  Γ ∣ Δ ⊢ case v (app m₁ (renameVal succ w)) (app m₂ (renameVal succ w)) ∶ B := by
  cases hcase with | case hv hm₁ hm₂ =>
  exact .case hv (.app hm₁ (wtWeakenVal hw)) (.app hm₂ (wtWeakenVal hw))

theorem wtCaseFst {Γ δ} {Δ : Dtxt δ} {v m₁ m₂ B₁ B₂} (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊢ case v (fst m₁) (fst m₂) ∶ B₁ := by
  cases hcase with | case hv hm₁ hm₂ =>
  exact .case hv (.fst hm₁) (.fst hm₂)

theorem wtCaseSnd {Γ δ} {Δ : Dtxt δ} {v m₁ m₂ B₁ B₂} (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊢ case v (snd m₁) (snd m₂) ∶ B₂ := by
  cases hcase with | case hv hm₁ hm₂ =>
  exact .case hv (.snd hm₁) (.snd hm₂)
