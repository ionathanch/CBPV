import CBPV.Typing
import CBPV.Rejoin

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

def 𝒞 {δ} (B : ComType) (m : Com δ) : Prop :=
  match B with
  | F A => ∃ v, 𝒱 A v ∧ m = ret v
  | Arr A B => ∃ n, (∀ v, 𝒱 A v → ℰ B (n⦃v⦄)) ∧ m = lam n
  | .Prod B₁ B₂ => ∃ n₁ n₂, ℰ B₁ n₁ ∧ ℰ B₂ n₂ ∧ m = prod n₁ n₂

def ℰ {δ} (B : ComType) (m : Com δ) := ∃ n, m ⇓ₙ n ∧ 𝒞 B n
end
notation:40 v:41 "∈" "⟦" A:41 "⟧ᵛ" => 𝒱 A v
notation:40 m:41 "∈" "⟦" B:41 "⟧ᶜ" => 𝒞 B m
notation:40 m:41 "∈" "⟦" B:41 "⟧ᵉ" => ℰ B m

/-* Semantic computations are normal and embed into semantic evaluations *-/

theorem 𝒞.nf {δ B m} (h : m ∈ ⟦ B ⟧ᶜ) : @nf δ m :=
  match (generalizing := true) B with
  | F _ | Arr _ _ =>
    by unfold 𝒞 at h; let ⟨_, _, e⟩ := h; subst e; exact ⟨⟩
  | .Prod _ _ =>
    by unfold 𝒞 at h; let ⟨_, _, _, _, e⟩ := h; subst e; exact ⟨⟩

theorem 𝒞ℰ {δ B} {m : Com δ} (h : m ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ :=
  by unfold ℰ; exact ⟨m, ⟨.refl, 𝒞.nf h⟩, h⟩

/-* Convenient constructors for the logical relation *-/

theorem 𝒱.unit : 𝒱 Unit unit := by simp [𝒱]
theorem 𝒱.inl {v A₁ A₂} (h : v ∈ ⟦A₁⟧ᵛ) : inl v ∈ ⟦Sum A₁ A₂⟧ᵛ := by simp [𝒱, h]
theorem 𝒱.inr {v A₁ A₂} (h : v ∈ ⟦A₂⟧ᵛ) : inr v ∈ ⟦Sum A₁ A₂⟧ᵛ := by simp [𝒱, h]
theorem 𝒱.thunk {m B} (h : m ∈ ⟦B⟧ᵉ) : thunk m ∈ ⟦U B⟧ᵛ := by simp [𝒱, h]
theorem ℰ.ret {δ v A} (h : v ∈ ⟦A⟧ᵛ) : @ret δ v ∈ ⟦F A⟧ᵉ := by apply 𝒞ℰ; simp [𝒞, h]
theorem ℰ.lam {δ n A B} (h : ∀ v, v ∈ ⟦A⟧ᵛ → n⦃v⦄ ∈ ⟦B⟧ᵉ) : @lam δ n ∈ ⟦Arr A B⟧ᵉ := by apply 𝒞ℰ; simp [𝒞]; exact h
theorem ℰ.prod {δ m n B₁ B₂} (hm : m ∈ ⟦B₁⟧ᵉ) (hn : n ∈ ⟦B₂⟧ᵉ) : @prod δ m n ∈ ⟦Prod B₁ B₂⟧ᵉ := by apply 𝒞ℰ; simp [𝒞]; exact ⟨hm, hn⟩

/-* Semantic evaluations are backward closed under reduction *-/

theorem ℰ.bwds {δ B} {m n : Com δ} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᵉ) : m ∈ ⟦ B ⟧ᵉ := by
  unfold ℰ at *
  let ⟨n', nn', h⟩ := h
  exact ⟨n', nn'.bwds r, h⟩

theorem ℰ.bwdsRejoin {δ B js} {m n : Com 0} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᵉ) : rejoin (weakenJCom δ m) js ∈ ⟦ B ⟧ᵉ := by
  unfold ℰ at *
  let ⟨n', nn', h⟩ := h
  exact ⟨n', nn'.bwdsRejoin r, h⟩

theorem ℰ.bwdsRejoin0 {δ B js} {m n : Com 0} (r : m ⇒⋆ weakenJCom 0 n) (h : n ∈ ⟦ B ⟧ᵉ) : rejoin (weakenJCom δ m) js ∈ ⟦ B ⟧ᵉ := by
  rw [weakenJCom0] at r; exact h.bwdsRejoin r

theorem ℰ.bwd {δ B} {m n : Com δ} (r : m ⇒ n) : n ∈ ⟦ B ⟧ᵉ → m ∈ ⟦ B ⟧ᵉ := ℰ.bwds (.once r)
theorem ℰ.bwdRejoin {δ B js} {m n : Com 0} (r : m ⇒ n) : n ∈ ⟦ B ⟧ᵉ → rejoin (weakenJCom δ m) js ∈ ⟦ B ⟧ᵉ := ℰ.bwdsRejoin (.once r)
theorem ℰ.bwdRejoin0 {δ B js} {m n : Com 0} (r : m ⇒ weakenJCom 0 n) : n ∈ ⟦ B ⟧ᵉ → rejoin (weakenJCom δ m) js ∈ ⟦ B ⟧ᵉ := ℰ.bwdsRejoin0 (.once r)

/-*----------------
  Semantic typing
----------------*-/

/-* Semantic well-formedness of contexts *-/

def semCtxt Γ (σ : Nat → Val) := ∀ {x A}, Γ ∋ x ∶ A → σ x ∈ ⟦ A ⟧ᵛ
notation:40 Γ:41 "⊨" σ:41 => semCtxt Γ σ

theorem semCtxt.nil : ⬝ ⊨ var := by intro _ _ mem; cases mem
theorem semCtxt.cons {Γ σ v A} (h : v ∈ ⟦ A ⟧ᵛ) (hσ : Γ ⊨ σ) : Γ ∷ A ⊨ v +: σ
  | _, _, .here => h
  | _, _, .there mem => hσ mem

/-* Semantic well-formedness of join point contexts *-/

section
set_option hygiene false
local notation:40 Δ:41 "⊨" js:41 => semDtxt Δ js
inductive semDtxt : ∀ {δ}, Dtxt δ → J δ → Prop where
  | nil : ⬝ ⊨ .nil
  | cons {δ} {Δ : Dtxt δ} {js m A B} : Δ ⊨ js →
    (∀ {v}, v ∈ ⟦ A ⟧ᵛ → (rejoin (m⦃v⦄) js) ∈ ⟦ B ⟧ᵉ) →
    Δ ∷ A ↗ B ⊨ .cons m js
end
notation:40 Δ:41 "⊨" js:41 => semDtxt Δ js

/-* Semantic typing of values and computations *-/

@[simp] def semVal (Γ : Ctxt) v A := ∀ σ, Γ ⊨ σ → v⦃σ⦄ ∈ ⟦ A ⟧ᵛ
@[simp] def semCom (Γ : Ctxt) {δ} (Δ : Dtxt δ) m B := ∀ σ, Γ ⊨ σ → ∀ js, Δ ⊨ js → rejoin (m⦃σ⦄) js ∈ ⟦ B ⟧ᵉ
notation:40 Γ:41 "⊨" v:41 "∶" A:41 => semVal Γ v A
notation:40 Γ:41 "∣" Δ:41 "⊨" m:41 "∶" B:41 => semCom Γ Δ m B

/-*----------------------------------------
  Fundamental theorem of soundness
  of syntactic typing wrt semantic typing
----------------------------------------*-/

theorem rejoinJump {Γ : Ctxt} {δ} {Δ : Dtxt δ} {js j A B} (mem : Δ ∋ j ∶ A ↗ B) (h : Δ ⊨ js) :
  ∀ {σ v}, Γ ⊨ σ → v ∈ ⟦ A ⟧ᵛ → (rejoin (jump j v) js) ∈ ⟦ B ⟧ᵉ := by
  induction h generalizing A B
  case nil => cases mem
  case cons h _ =>
    cases mem
    case here =>
      intro σ v hσ hv; simp
      exact .bwd (.rejoin .γ) (h hv)
    case there ih _ mem =>
      intro σ v hσ hv; simp
      exact .bwd (.rejoin .join't) (ih mem hσ hv)

theorem soundness {Γ} :
  (∀ (v : Val) A, Γ ⊢ v ∶ A → Γ ⊨ v ∶ A) ∧
  (∀ {δ Δ} (m : Com δ) B, Γ ∣ Δ ⊢ m ∶ B → Γ ∣ Δ ⊨ m ∶ B) := by
  refine ⟨λ v A h ↦ ?val, λ m B h ↦ ?com⟩
  mutual_induction h, h
  all_goals intro σ hσ
  case var mem => exact hσ mem
  case unit => exact 𝒱.unit
  case inl ih => exact 𝒱.inl (ih σ hσ)
  case inr ih => exact 𝒱.inr (ih σ hσ)
  case thunk ih => exact 𝒱.thunk (ih σ hσ .nil .nil)
  all_goals intro js hjs
  case force ih =>
    simp [𝒱] at ih
    let ⟨m, h, e⟩ := ih σ hσ
    simp [e]; exact ℰ.bwdRejoin0 .π h
  case lam m _ _ _ ih =>
    refine ℰ.bwdsRejoin0 (n := (lam m)⦃σ⦄) .refl (ℰ.lam (λ v hv ↦ ?hB))
    rw [substUnion]
    exact ih (v +: σ) (semCtxt.cons hv hσ) .nil .nil
  case app v _ _ _ _ ihm ihv =>
    simp [ℰ] at ihm; simp [𝒞] at ihm
    let ⟨_, ⟨rlam, _⟩, n, h, e⟩ := ihm σ hσ .nil .nil; subst e
    exact ℰ.bwdsRejoin0 (js := js) (.trans' (Evals.app rlam) (.once .β)) (h _ (ihv σ hσ))
  case ret ih => exact ℰ.bwdsRejoin0 .refl (ℰ.ret (ih σ hσ))
  case letin ihret ih =>
    simp [ℰ, 𝒞] at ihret
    let ⟨_, ⟨rret, _⟩, v, hv, e⟩ := ihret σ hσ .nil .nil; subst e
    let h := ih (v +: σ) (semCtxt.cons hv hσ) js hjs
    rw [← substUnion] at h
    exact ℰ.bwds (Evals.rejoin (.trans' (Evals.letin rret) (.once .ζ))) h
  case case ihv ihm ihn =>
    simp [𝒱] at ihv
    match ihv σ hσ with
    | .inl ⟨v, hv, e⟩ =>
      let hm := ihm (v +: σ) (semCtxt.cons hv hσ) js hjs
      simp [e]; rw [← substUnion] at hm
      exact ℰ.bwd (.rejoin .ιl) hm
    | .inr ⟨v, hv, e⟩ =>
      let hn := ihn (v +: σ) (semCtxt.cons hv hσ) js hjs
      simp [e]; rw [← substUnion] at hn
      exact ℰ.bwd (.rejoin .ιr) hn
  case prod ihm ihn =>
    exact ℰ.bwdsRejoin0 .refl (ℰ.prod (ihm σ hσ .nil .nil) (ihn σ hσ .nil .nil))
  case fst ih =>
    simp [ℰ] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, _⟩, n₁, n₂, hm, _, e⟩ := ih σ hσ .nil .nil; subst e
    exact ℰ.bwdsRejoin0 (.trans' (Evals.fst rprod) (.once .π1)) hm
  case snd ih =>
    simp [ℰ] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, nfprod⟩, n₁, n₂, _, hn, e⟩ := ih σ hσ .nil .nil; subst e
    exact ℰ.bwdsRejoin0 (.trans' (Evals.snd rprod) (.once .π2)) hn
  case join m _ _ _ _ _ ihm ihn =>
    let hn := ihn σ hσ (.cons (m⦃⇑ σ⦄) js) (.cons hjs (λ {v} hv ↦ ?hm))
    case hm =>
      rw [substUnion]
      exact ihm (v +: σ) (semCtxt.cons hv hσ) js hjs
    exact hn
  case jump mem _ ihv => exact rejoinJump mem hjs hσ (ihv σ hσ)

-- If a computation does not step, then it is in normal form
theorem normal {m B} (nr : ∀ {n}, ¬ m ⇒ n) (h : ⬝ ∣ ⬝ ⊢ m ∶ B) : nf m := by
  let ⟨_, soundCom⟩ := soundness (Γ := ⬝)
  let mB := soundCom m B h
  simp [ℰ] at mB
  let ⟨_, ⟨r, nfm⟩, _⟩ := mB var semCtxt.nil .nil .nil
  rw [substComId] at r
  cases r with | refl => exact nfm | trans r _ => cases nr r

-- Computations are strongly normalizing
theorem normalization {m : Com 0} {B : ComType} (h : ⬝ ∣ ⬝ ⊢ m ∶ B) : SN m := by
  let ⟨_, soundCom⟩ := soundness (Γ := ⬝)
  let mB := soundCom m B h
  simp [ℰ] at mB
  let ⟨_, ⟨r, nfm⟩, _⟩ := mB var semCtxt.nil .nil .nil
  rw [substComId] at r
  exact r.sn nfm
