import CBPV.Evaluation
import CBPV.Typing

open Nat ValType ComType Val Com

/-*--------------------------
  Logical relation on types
--------------------------*-/

mutual
def 𝒱 (A : ValType) (v : Val) : Prop :=
  match A with
  | .Unit => v = unit
  | .Sum A₁ A₂ => (∃ w, 𝒱 A₁ w ∧ v = inl w) ∨ (∃ w, 𝒱 A₂ w ∧ v = inr w)
  | U B => ∃ m, ℰ B m ∧ v = thunk m

def 𝒞 (B : ComType) (m : Com) : Prop :=
  match B with
  | F A => ∃ v, 𝒱 A v ∧ m = ret v
  | Arr A B => ∃ n, (∀ v, 𝒱 A v → ℰ B (n⦃v⦄)) ∧ m = lam n
  | .Prod B₁ B₂ => ∃ n₁ n₂, ℰ B₁ n₁ ∧ ℰ B₂ n₂ ∧ m = prod n₁ n₂

def ℰ (B : ComType) (m : Com) := ∃ n, m ⇓ₙ n ∧ 𝒞 B n
end
notation:40 v:41 "∈" "⟦" A:41 "⟧ᵛ" => 𝒱 A v
notation:40 m:41 "∈" "⟦" B:41 "⟧ᶜ" => 𝒞 B m
notation:40 m:41 "∈" "⟦" B:41 "⟧ᵉ" => ℰ B m

-- Convenient constructors for the logical relation
theorem 𝒱.unit : 𝒱 Unit unit := by simp [𝒱]
theorem 𝒱.inl {v A₁ A₂} (h : 𝒱 A₁ v) : 𝒱 (Sum A₁ A₂) (inl v) := by simp [𝒱]; assumption
theorem 𝒱.inr {v A₁ A₂} (h : 𝒱 A₂ v) : 𝒱 (Sum A₁ A₂) (inr v) := by simp [𝒱]; assumption
theorem 𝒱.thunk {m B} (h : ℰ B m) : 𝒱 (U B) (thunk m) := by simp [𝒱]; assumption
theorem 𝒞.ret {v A} (h : 𝒱 A v) : 𝒞 (F A) (ret v) := by simp [𝒞]; assumption
theorem 𝒞.lam {n A B} (h : ∀ v, 𝒱 A v → ℰ B (n⦃v⦄)) : 𝒞 (Arr A B) (lam n) := by simp [𝒞]; assumption
theorem 𝒞.prod {m n B₁ B₂} (hm : ℰ B₁ m) (hn : ℰ B₂ n) : 𝒞 (Prod B₁ B₂) (prod m n) := by simp [𝒞]; constructor <;> assumption

-- Semantic computations are normal
theorem 𝒞nf {B m} (h : m ∈ ⟦ B ⟧ᶜ) : nf m :=
  match (generalizing := true) B with
  | F _ | Arr _ _ =>
    by unfold 𝒞 at h; let ⟨_, _, e⟩ := h; subst e; exact ⟨⟩
  | .Prod _ _ =>
    by unfold 𝒞 at h; let ⟨_, _, _, _, e⟩ := h; subst e; exact ⟨⟩

-- Semantic computations embed into semantic evaluations
theorem 𝒞ℰ {B m} (h : m ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ :=
  by unfold ℰ; exact ⟨m, ⟨.refl, 𝒞nf h⟩, h⟩

-- Semantic evaluations are backward closed under reduction
theorem ℰbwd {B m n} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᵉ) : m ∈ ⟦ B ⟧ᵉ := by
  unfold ℰ at *
  let ⟨n', ⟨r', nfn⟩, h⟩ := h
  refine ⟨n', ⟨.trans' r r', nfn⟩, h⟩
theorem 𝒞bwd {B m n} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ := ℰbwd r (𝒞ℰ h)

/-*----------------
  Semantic typing
----------------*-/

def semCtxt Γ (σ : Nat → Val) := ∀ {x A}, Γ ∋ x ∶ A → σ x ∈ ⟦ A ⟧ᵛ
notation:40 Γ:41 "⊨" σ:41 => semCtxt Γ σ

theorem semCtxtNil : ⬝ ⊨ var := by intro _ _ mem; cases mem
theorem semCtxtCons {Γ σ v A} (h : v ∈ ⟦ A ⟧ᵛ) (hσ : Γ ⊨ σ) : Γ ∷ A ⊨ v +: σ
  | _, _, .here => h
  | _, _, .there mem => hσ mem

def semDtxt Γ Δ (τ : Nat → Com) := ∀ {σ j v A B}, Γ ⊨ σ → Δ ∋ j ∶ A ↗ B → v ∈ ⟦ A ⟧ᵛ → (τ j)⦃v +: σ⦄ ∈ ⟦ B ⟧ᵉ
notation:40 Γ:41 "∣" Δ:41 "⊨" τ:41 => semDtxt Γ Δ τ

theorem semDtxtNil {Γ} {τ : Nat → Com} : Γ ∣ ⬝ ⊨ τ := λ _ mem ↦ by cases mem

theorem semDtxtCons₁ {Γ Δ τ A} (hτ : Γ ∣ Δ ⊨ τ) : Γ ∷ A ∣ Δ ⊨ renameCom (lift succ) ∘ τ := by
  intro σ j v _ _ hσ mem; simp
  rw [substRenameCom, substComExt _ (v +: σ ∘ succ) (λ n ↦ ?e)]
  case e => cases n <;> simp [lift]
  exact hτ (λ mem ↦ hσ (.there mem)) mem

theorem semDtxtCons₂ {Γ Δ τ m A B} (h : ∀ {σ v}, Γ ⊨ σ → v ∈ ⟦ A ⟧ᵛ → m⦃v +: σ⦄ ∈ ⟦ B ⟧ᵉ) (hτ : Γ ∣ Δ ⊨ τ) : Γ ∣ Δ ∷ A ↗ B ⊨ m +: τ := by
  intro _ _ _ _ _ hσ mem; cases mem
  case here => exact h hσ
  case there mem => exact hτ hσ mem

-- Semantic typing of values and computations
@[simp] def semVal (Γ : Ctxt) v A := ∀ σ, Γ ⊨ σ → v⦃σ⦄ ∈ ⟦ A ⟧ᵛ
@[simp] def semCom (Γ : Ctxt) (Δ : Dtxt) m B := ∀ σ, Γ ⊨ σ → ∀ τ, Γ ∣ Δ ⊨ τ → (substJoin τ m)⦃σ⦄ ∈ ⟦ B ⟧ᵉ
notation:40 Γ:41 "⊨" v:41 "∶" A:41 => semVal Γ v A
notation:40 Γ:41 "∣" Δ:41 "⊨" m:41 "∶" B:41 => semCom Γ Δ m B

/-*----------------------------------------
  Fundamental theorem of soundness
  of syntactic typing wrt semantic typing
----------------------------------------*-/

theorem soundness {Γ} :
  (∀ (v : Val) A, Γ ⊢ v ∶ A → Γ ⊨ v ∶ A) ∧
  (∀ {Δ} (m : Com) B, Γ ∣ Δ ⊢ m ∶ B → Γ ∣ Δ ⊨ m ∶ B) := by
  refine ⟨λ v A h ↦ ?val, λ m B h ↦ ?com⟩
  mutual_induction h, h
  all_goals intro σ hσ
  case var mem => exact hσ mem
  case unit => exact 𝒱.unit
  case inl ih => exact 𝒱.inl (ih σ hσ)
  case inr ih => exact 𝒱.inr (ih σ hσ)
  case thunk ih =>
    let hm := ih σ hσ jid semDtxtNil
    rw [substJid] at hm; exact 𝒱.thunk hm
  all_goals intro τ hτ
  case force ih =>
    simp [𝒱, ℰ] at ih
    let ⟨_, ⟨_, ⟨r, _⟩, h⟩, e⟩ := ih σ hσ
    let rf : _ ⇒⋆ _ := .trans .π r
    rw [← e] at rf; exact 𝒞bwd rf h
  case lam ih =>
    apply 𝒞ℰ; apply 𝒞.lam
    intro v hv; rw [← substUnion]
    let hm := ih (v +: σ) (semCtxtCons hv hσ) jid semDtxtNil
    rw [substJid] at hm; exact hm
  case app ihm ihv =>
    simp [ℰ, 𝒞] at ihm
    let ⟨_, ⟨rlam, _⟩, _, h, e⟩ := ihm σ hσ jid semDtxtNil; subst e
    let ⟨_, ⟨rval, _⟩, h⟩ := h _ (ihv σ hσ)
    rw [substJid] at rlam
    exact 𝒞bwd (Trans.trans (Evals.app rlam) (Trans.trans Eval.β rval)) h
  case ret ih => exact 𝒞ℰ (𝒞.ret (ih σ hσ))
  case letin n _ _ _ _ ihret ih =>
    simp [ℰ, 𝒞] at ihret ih
    let ⟨_, ⟨rret, _⟩, v, hv, e⟩ := ihret σ hσ jid semDtxtNil; subst e
    let ⟨_, ⟨rlet, nflet⟩, h⟩ := ih (v +: σ) (semCtxtCons hv hσ) _ (semDtxtCons₁ hτ)
    rw [substUnion] at rlet
    rw [substJid] at rret
    exact 𝒞bwd (Trans.trans (Evals.let rret) (Trans.trans Eval.ζ rlet)) h
  case case m n _ _ _ _ _ _ ihv ihm ihn =>
    simp [𝒱] at ihv
    match ihv σ hσ with
    | .inl ⟨v, hv, e⟩ =>
      let hm := ihm (v +: σ) (semCtxtCons hv hσ) _ (semDtxtCons₁ hτ)
      simp [substJoin, substCom]; rw [e]; rw [substUnion] at hm
      exact ℰbwd (.once .ιl) hm
    | .inr ⟨v, hv, e⟩ =>
      let hn := ihn (v +: σ) (semCtxtCons hv hσ) _ (semDtxtCons₁ hτ)
      simp [substJoin, substCom]; rw [e]; rw [substUnion] at hn
      exact ℰbwd (.once .ιr) hn
  case prod m n _ _ _ _ ihm ihn =>
    simp [ℰ, 𝒞] at ihm ihn
    let ⟨_, ⟨rm, _⟩, hm⟩ := ihm σ hσ jid semDtxtNil
    let ⟨_, ⟨rn, _⟩, hn⟩ := ihn σ hσ jid semDtxtNil
    rw [substJid] at rm rn
    apply 𝒞ℰ; exact 𝒞.prod (𝒞bwd rm hm) (𝒞bwd rn hn)
  case fst ih =>
    simp [ℰ] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, nfprod⟩, n₁, n₂, hm, _, e⟩ := ih σ hσ jid semDtxtNil; subst e
    rw [substJid] at rprod
    let r : fst (_⦃σ⦄) ⇒⋆ n₁ := Trans.trans (Evals.fst rprod) Eval.π1
    exact ℰbwd r hm
  case snd ih =>
    simp [ℰ] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, nfprod⟩, n₁, n₂, _, hn, e⟩ := ih σ hσ jid semDtxtNil; subst e
    rw [substJid] at rprod
    let r : snd (_⦃σ⦄) ⇒⋆ n₂ := Trans.trans (Evals.snd rprod) Eval.π2
    exact ℰbwd r hn
  case join Γ Δ m _ A B _ _ ihm ihn =>
    simp [ℰ] at ihn
    let hm := λ {σ v} hσ hv ↦ ihm (v +: σ) (semCtxtCons hv hσ) _ (semDtxtCons₁ hτ)
    let ⟨n, ⟨r, _⟩, hn⟩ := ihn σ hσ _ (semDtxtCons₂ hm hτ)
    refine 𝒞bwd ?_ hn
    simp; sorry
  case jump j v _ _ mem _ ihv =>
    simp [substJoin, substPush]
    exact hτ hσ mem (ihv σ hσ)

-- If a computation does not step, then it is in normal form
theorem normal {m B} (nr : ∀ {n}, ¬ m ⇒ n) (h : ⬝ ∣ ⬝ ⊢ m ∶ B) : nf m := by
  let ⟨_, soundCom⟩ := soundness (Γ := ⬝)
  let mB := soundCom m B h
  simp [ℰ] at mB
  let ⟨_, ⟨r, nfm⟩, _⟩ := mB var semCtxtNil jid semDtxtNil
  rw [substComId, substJid] at r
  cases r with | refl => exact nfm | trans r _ => cases nr r

-- Computations are strongly normalizing
theorem normalization {m : Com} {B : ComType} (h : ⬝ ∣ ⬝ ⊢ m ∶ B) : SN m := by
  let ⟨_, soundCom⟩ := soundness (Γ := ⬝)
  let mB := soundCom m B h
  simp [ℰ] at mB
  let ⟨_, ⟨r, nfm⟩, _⟩ := mB var semCtxtNil jid semDtxtNil
  rw [substComId, substJid] at r
  exact r.sn nfm
