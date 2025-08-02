import CBPV.Typing
import CBPV.Rejoin

open Nat ValType ComType Val Com

/-*----------------------------------
  Logical equivalence (LE) of terms
----------------------------------*-/

mutual
def 𝒱 (A : ValType) (v : Val) (w : Val) : Prop :=
  match A with
  | .Unit => v = unit ∧ w = unit
  | .Sum A₁ A₂ =>
    (∃ v' w', 𝒱 A₁ v' w' ∧ v = inl v' ∧ w = inl w') ∨
    (∃ v' w', 𝒱 A₂ v' w' ∧ v = inr v' ∧ w = inr w')
  | U B => ∃ m n, ℰ B m n ∧ v = thunk m ∧ w = thunk n

def 𝒞 (B : ComType) (m : Com) (n : Com) : Prop :=
  match B with
  | F A => ∃ v w, 𝒱 A v w ∧ m = ret v ∧ n = ret w
  | Arr A B => ∃ m' n', (∀ v w, 𝒱 A v w → ℰ B (m'⦃v⦄) (n'⦃w⦄)) ∧
    m = lam m' ∧ n = lam n'
  | .Prod B₁ B₂ => ∃ m₁ m₂ n₁ n₂, ℰ B₁ m₁ n₁ ∧ ℰ B₂ m₂ n₂ ∧
    m = prod m₁ m₂ ∧ n = prod n₁ n₂

def ℰ (B : ComType) (m : Com) (n : Com) :=
  ∃ m' n', m ⇓ₙ m' ∧ n ⇓ₙ n' ∧ 𝒞 B m' n'
end

notation:40 "(" v:41 "," w:41 ")" "∈" "⟦" A:41 "⟧ᵛ" => 𝒱 A v w
notation:40 "(" m:41 "," n:41 ")" "∈" "⟦" B:41 "⟧ᶜ" => 𝒞 B m n
notation:40 "(" m:41 "," n:41 ")" "∈" "⟦" B:41 "⟧ᵉ" => ℰ B m n

/-* LE computations are normal and embed into LE evaluations *-/

theorem 𝒞.nf {m n B} (h : (m, n) ∈ ⟦B⟧ᶜ) : nf m ∧ nf n := by
  match (generalizing := true) B with
  | F _ | Arr _ _ => unfold 𝒞 at h; let ⟨_, _, _, e₁, e₂⟩ := h; simp [e₁, e₂]
  | .Prod _ _ => unfold 𝒞 at h; let ⟨_, _, _, _, _, _, e₁, e₂⟩ := h; simp [e₁, e₂]

theorem 𝒞ℰ {m n A} (h : 𝒞 A m n) : ℰ A m n := by
  unfold ℰ; let ⟨nfm, nfn⟩ := h.nf; exact ⟨m, n, .refl nfm, .refl nfn, h⟩

/-*-------------------------------
  Convenient constructors for LE
-------------------------------*-/

theorem 𝒱.unit : 𝒱 Unit unit unit := by simp [𝒱]
theorem 𝒱.inl {v w A₁ A₂} (h : (v, w) ∈ ⟦A₁⟧ᵛ) : (inl v, inl w) ∈ ⟦Sum A₁ A₂⟧ᵛ := by simp [𝒱, h]
theorem 𝒱.inr {v w A₁ A₂} (h : (v, w) ∈ ⟦A₂⟧ᵛ) : (inr v, inr w) ∈ ⟦Sum A₁ A₂⟧ᵛ := by simp [𝒱, h]
theorem 𝒱.thunk {m n B} (h : (m, n) ∈ ⟦B⟧ᵉ) : (thunk m, thunk n) ∈ ⟦U B⟧ᵛ := by simp [𝒱, h]

namespace ℰ

theorem ret {v w A} (h : (v, w) ∈ ⟦A⟧ᵛ) : (ret v, ret w) ∈ ⟦F A⟧ᵉ := by
  apply 𝒞ℰ; simp [ℰ, 𝒞, h]

theorem lam {m n A B} (h : ∀ v w, (v, w) ∈ ⟦A⟧ᵛ → (m⦃v⦄, n⦃w⦄) ∈ ⟦B⟧ᵉ) : (lam m, lam n) ∈ ⟦Arr A B⟧ᵉ := by
  apply 𝒞ℰ; simp [ℰ, 𝒞] at *; exact h

theorem prod {m₁ m₂ n₁ n₂ B₁ B₂} (hB₁ : (m₁, n₁) ∈ ⟦B₁⟧ᵉ) (hB₂ : (m₂, n₂) ∈ ⟦B₂⟧ᵉ) : (prod m₁ m₂, prod n₁ n₂) ∈ ⟦Prod B₁ B₂⟧ᵉ:= by
  apply 𝒞ℰ; unfold 𝒞; exact ⟨_, _, _, _, hB₁, hB₂, rfl, rfl⟩

/-*-----------------------
  Inversion lemmas on LE
-----------------------*-/

theorem ret_inv {m n A} (h : (m, n) ∈ ⟦F A⟧ᵉ) : ∃ v w, m ⇒⋆ .ret v ∧ n ⇒⋆ .ret w ∧ (v, w) ∈ ⟦A⟧ᵛ := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, h, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, r₁, r₂, h⟩

theorem lam_inv {m₁ m₂ A B} (h : (m₁, m₂) ∈ ⟦Arr A B⟧ᵉ) : ∃ n₁ n₂, m₁ ⇒⋆ .lam n₁ ∧ m₂ ⇒⋆ .lam n₂ ∧ (∀ v w, (v, w) ∈ ⟦A⟧ᵛ → (n₁⦃v⦄, n₂⦃w⦄) ∈ ⟦B⟧ᵉ) := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, h, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, r₁, r₂, h⟩

theorem prod_inv {m n B₁ B₂} (h : (m, n) ∈ ⟦Prod B₁ B₂⟧ᵉ) : ∃ m₁ m₂ n₁ n₂, m ⇒⋆ .prod m₁ m₂ ∧ n ⇒⋆ .prod n₁ n₂ ∧ (m₁, n₁) ∈ ⟦B₁⟧ᵉ ∧ (m₂, n₂) ∈ ⟦B₂⟧ᵉ := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, _, _, h₁, h₂, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, _, _, r₁, r₂, h₁, h₂⟩

theorem fst {m n B₁ B₂} (h : (m, n) ∈ ⟦Prod B₁ B₂⟧ᵉ) : ∃ m₁ m₂ n₁ n₂, m ⇒⋆ .prod m₁ m₂ ∧ n ⇒⋆ .prod n₁ n₂ ∧ (m₁, n₁) ∈ ⟦B₁⟧ᵉ := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, _, _, h, _, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, _, _, r₁, r₂, h⟩

theorem snd {m n B₁ B₂} (h : (m, n) ∈ ⟦Prod B₁ B₂⟧ᵉ) : ∃ m₁ m₂ n₁ n₂, m ⇒⋆ .prod m₁ m₂ ∧ n ⇒⋆ .prod n₁ n₂ ∧ (m₂, n₂) ∈ ⟦B₂⟧ᵉ := by
  unfold ℰ 𝒞 at h
  let ⟨_, _, ⟨r₁, _⟩, ⟨r₂, _⟩, _, _, _, _, _, h, e₁, e₂⟩ := h
  subst e₁ e₂; exact ⟨_, _, _, _, r₁, r₂, h⟩

end ℰ

/-*------------
  LE is a PER
------------*-/

theorem sym𝒞ℰ {B} (𝒞sym : ∀ {m n}, (m, n) ∈ ⟦B⟧ᶜ → (n, m) ∈ ⟦B⟧ᶜ) :
  ∀ {m n}, (m, n) ∈ ⟦B⟧ᵉ → (n, m) ∈ ⟦B⟧ᵉ := by
  intro _ _ h
  unfold ℰ at *
  let ⟨_, _, nm, nn, hB⟩ := h
  exact ⟨_, _, nn, nm, 𝒞sym hB⟩

theorem sym𝒱𝒞 :
  (∀ {v w A}, (v, w) ∈ ⟦A⟧ᵛ → (w, v) ∈ ⟦A⟧ᵛ) ∧
  (∀ {m n B}, (m, n) ∈ ⟦B⟧ᶜ → (n, m) ∈ ⟦B⟧ᶜ) := by
  refine ⟨λ {v w A} h ↦ ?val, λ {m n B} h ↦ ?com⟩
  mutual_induction A, B
  case Unit => unfold 𝒱 at *; simp [h]
  case Sum ihA₁ ihA₂ =>
    unfold 𝒱; unfold 𝒱 at h
    match h with
    | .inl ⟨_, _, hA₁, ev, ew⟩ => refine .inl ⟨_, _, ihA₁ hA₁, ew, ev⟩
    | .inr ⟨_, _, hA₂, ev, ew⟩ => refine .inr ⟨_, _, ihA₂ hA₂, ew, ev⟩
  case U ih =>
    unfold 𝒱 at *
    let ⟨_, _, hA, ev, ew⟩ := h
    exact ⟨_, _, sym𝒞ℰ ih hA, ew, ev⟩
  case F ih =>
    unfold 𝒞 at *
    let ⟨_, _, hB, em, en⟩ := h
    exact ⟨_, _, ih hB, en, em⟩
  case Arr ihA ihB =>
    unfold 𝒞; unfold 𝒞 at h
    let ⟨_, _, hB, em, en⟩ := h
    exact ⟨_, _, λ v w hA ↦ sym𝒞ℰ ihB (hB _ _ (ihA hA)), en, em⟩
  case Prod ihB₁ ihB₂ =>
    unfold 𝒞; unfold 𝒞 at h
    let ⟨_, _, _, _, hB₁, hB₂, em, en⟩ := h
    exact ⟨_, _, _, _, sym𝒞ℰ ihB₁ hB₁, sym𝒞ℰ ihB₂ hB₂, en, em⟩

def 𝒱.sym := @sym𝒱𝒞.left
def 𝒞.sym := @sym𝒱𝒞.right
def ℰ.sym {B} := @sym𝒞ℰ B 𝒞.sym

theorem trans𝒞ℰ {B} (𝒞trans : ∀ {m₁ m₂ m₃}, (m₁, m₂) ∈ ⟦B⟧ᶜ → (m₂, m₃) ∈ ⟦B⟧ᶜ → (m₁, m₃) ∈ ⟦B⟧ᶜ) :
  ∀ {m₁ m₂ m₃}, (m₁, m₂) ∈ ⟦B⟧ᵉ → (m₂, m₃) ∈ ⟦B⟧ᵉ → (m₁, m₃) ∈ ⟦B⟧ᵉ := by
  intro _ _ _ h₁₂ h₂₃
  unfold ℰ at *
  let ⟨m, m', nm, nm', hB₁₂⟩ := h₁₂
  let ⟨n', n, nn', nn, hB₂₃⟩ := h₂₃
  rw [Norm.join nm' nn'] at hB₁₂
  exact ⟨m, n, nm, nn, 𝒞trans hB₁₂ hB₂₃⟩

theorem trans𝒱𝒞 :
  (∀ {v₁ v₂ v₃ A}, (v₁, v₂) ∈ ⟦A⟧ᵛ → (v₂, v₃) ∈ ⟦A⟧ᵛ → (v₁, v₃) ∈ ⟦A⟧ᵛ) ∧
  (∀ {m₁ m₂ m₃ B}, (m₁, m₂) ∈ ⟦B⟧ᶜ → (m₂, m₃) ∈ ⟦B⟧ᶜ → (m₁, m₃) ∈ ⟦B⟧ᶜ) := by
  refine ⟨λ {v₁ v₂ v₃ A} h₁₂ h₂₃ ↦ ?val, λ {m₁ m₂ m₃ B} h₁₂ h₂₃ ↦ ?com⟩
  mutual_induction A, B
  case Unit =>
    unfold 𝒱 at *
    let ⟨e₁, _⟩ := h₁₂
    let ⟨_, e₃⟩ := h₂₃
    exact ⟨e₁, e₃⟩
  case Sum ihA₁ ihA₂ =>
    unfold 𝒱; unfold 𝒱 at h₁₂ h₂₃
    match h₁₂, h₂₃ with
    | .inl ⟨_, _, hA₁₂, el₁, el₂⟩, .inl ⟨_, _, hA₂₃, er₂, er₃⟩ =>
      subst el₁ el₂ er₃; injection er₂ with e; subst e
      refine .inl ⟨_, _, ihA₁ hA₁₂ hA₂₃, rfl, rfl⟩
    | .inr ⟨_, _, hA₁₂, el₁, el₂⟩, .inr ⟨_, _, hA₂₃, er₂, er₃⟩ =>
      subst el₁ el₂ er₃; injection er₂ with e; subst e
      refine .inr ⟨_, _, ihA₂ hA₁₂ hA₂₃, rfl, rfl⟩
    | .inl ⟨_, _, _, _, er⟩, .inr ⟨_, _, _, _, _⟩ => subst er; contradiction
    | .inr ⟨_, _, _, _, er⟩, .inl ⟨_, _, _, _, _⟩ => subst er; contradiction
  case U ih =>
    unfold 𝒱 at *
    let ⟨_, _, hB₁₂, el₁, el₂⟩ := h₁₂
    let ⟨_, _, hB₂₃, er₂, er₃⟩ := h₂₃
    subst el₁ el₂ er₃; injection er₂ with e; subst e
    exact ⟨_, _, trans𝒞ℰ ih hB₁₂ hB₂₃, rfl, rfl⟩
  case F ih =>
    unfold 𝒞 at *
    let ⟨_, _, hA₁₂, el₁, el₂⟩ := h₁₂
    let ⟨_, _, hA₂₃, er₂, er₃⟩ := h₂₃
    subst el₁ el₂ er₃; injection er₂ with e; subst e
    exact ⟨_, _, ih hA₁₂ hA₂₃, rfl, rfl⟩
  case Arr ihA ihB =>
    unfold 𝒞; unfold 𝒞 at h₁₂ h₂₃
    let ⟨m, m', hB₁₂, el₁, el₂⟩ := h₁₂
    let ⟨_, n, hB₂₃, er₂, er₃⟩ := h₂₃
    subst el₁ el₂ er₃; injection er₂ with e; subst e
    refine ⟨_, _, λ v w hA ↦ ?_, rfl, rfl⟩
    apply trans𝒞ℰ ihB (hB₁₂ v w hA) (hB₂₃ w w (ihA hA.sym hA))
  case Prod ihB₁ ihB₂ =>
    unfold 𝒞; unfold 𝒞 at h₁₂ h₂₃
    let ⟨_, _, _, _, hA₁₁, hA₁₂, el₁, el₂⟩ := h₁₂
    let ⟨_, _, _, _, hA₂₁, hA₂₂, er₁, er₂⟩ := h₂₃
    subst el₁ el₂ er₂; injection er₁ with e₁ e₂; subst e₁ e₂
    refine ⟨_, _, _, _, trans𝒞ℰ ihB₁ hA₁₁ hA₂₁, trans𝒞ℰ ihB₂ hA₁₂ hA₂₂, rfl, rfl⟩

def 𝒱.trans := @trans𝒱𝒞.left
def 𝒞.trans := @trans𝒱𝒞.right
def ℰ.trans {B} := @trans𝒞ℰ B 𝒞.trans

/-*-----------------------------
  LE evals are backward closed
-----------------------------*-/

namespace ℰ

theorem bwds {m m' n n' B} (rm : m ⇒⋆ m') (rn : n ⇒⋆ n') (h : (m', n') ∈ ⟦B⟧ᵉ) : (m, n) ∈ ⟦B⟧ᵉ := by
  unfold ℰ at *
  let ⟨m'', n'', nm', nn', h⟩ := h
  exact ⟨m'', n'', nm'.bwds rm, nn'.bwds rn, h⟩

theorem bwdsRejoin {m m' n n' js₁ js₂ B} (rm : m ⇒⋆ m') (rn : n ⇒⋆ n') (h : (m', n') ∈ ⟦B⟧ᵉ) : (rejoin m js₁, rejoin n js₂) ∈ ⟦B⟧ᵉ := by
  unfold ℰ at *
  let ⟨m'', n'', nm', nn', h⟩ := h
  refine ⟨m'', n'', nm'.bwdsRejoin rm, nn'.bwdsRejoin rn, h⟩

theorem bwd {m m' n n' B} (rm : m ⇒ m') (rn : n ⇒ n') : (m', n') ∈ ⟦B⟧ᵉ → (m, n) ∈ ⟦B⟧ᵉ := ℰ.bwds (.once rm) (.once rn)
theorem bwdRejoin {m m' n n' js₁ js₂ B} (rm : m ⇒ m') (rn : n ⇒ n') : (m', n') ∈ ⟦B⟧ᵉ → (rejoin m js₁, rejoin n js₂) ∈ ⟦B⟧ᵉ := ℰ.bwdsRejoin (.once rm) (.once rn)

end ℰ

/-*---------------------
  Semantic equivalence
---------------------*-/

/-* Semantic equivalence of contexts as a PER *-/

def semCtxt Γ (σ τ : Nat → Val) := ∀ {x A}, Γ ∋ x ∶ A → (σ x, τ x) ∈ ⟦ A ⟧ᵛ
notation:40 Γ:41 "⊨" σ:41 "~" τ:41 => semCtxt Γ σ τ

namespace semCtxt

theorem nil : ⬝ ⊨ var ~ var := λ mem ↦ by cases mem
theorem cons {Γ σ τ v w A} (h : (v, w) ∈ ⟦ A ⟧ᵛ) (hστ : Γ ⊨ σ ~ τ) : Γ ∷ A ⊨ v +: σ ~ w +: τ
  | _, _, .here => h
  | _, _, .there mem => hστ mem

theorem sym {Γ σ τ} (h : Γ ⊨ σ ~ τ) : Γ ⊨ τ ~ σ := 𝒱.sym ∘ h
theorem trans {Γ ρ σ τ} (hρσ : Γ ⊨ ρ ~ σ) (hστ : Γ ⊨ σ ~ τ) : Γ ⊨ ρ ~ τ := λ mem ↦ 𝒱.trans (hρσ mem) (hστ mem)
theorem rename {ξ σ τ} {Γ Δ : Ctxt} (hξ : Γ ⊢ ξ ∶ Δ) (h : Γ ⊨ σ ~ τ) : Δ ⊨ σ ∘ ξ ~ τ ∘ ξ := h ∘ hξ _ _

end semCtxt

/-* Semantic equivalence of join point contexts as a PER *-/

section
set_option hygiene false
local notation:40 Δ:41 "⊨" js₁:41 "~" js₂:41 => semDtxt Δ js₁ js₂
inductive semDtxt : Dtxt → J → J → Prop where
  | nil : ⬝ ⊨ .nil ~ .nil
  | cons {Δ : Dtxt} {js₁ js₂ m n A B} : Δ ⊨ js₁ ~ js₂ →
    (∀ {v w}, (v, w) ∈ ⟦ A ⟧ᵛ → (rejoin (m⦃v⦄) js₁, rejoin (n⦃w⦄) js₂) ∈ ⟦ B ⟧ᵉ) →
    Δ ∷ A ↗ B ⊨ .cons m js₁ ~ .cons n js₂
end
notation:40 Δ:41 "⊨" js₁:41 "~" js₂:41 => semDtxt Δ js₁ js₂

theorem semDtxt.sym {Δ : Dtxt} {js₁ js₂} (h : Δ ⊨ js₁ ~ js₂) : Δ ⊨ js₂ ~ js₁ := by
  induction h
  case nil => exact .nil
  case cons h ih => exact .cons ih (λ hvw ↦  .sym (h hvw.sym))

theorem semDtxt.trans {Δ : Dtxt} {js₁ js₂ js₃} (h₁₂ : Δ ⊨ js₁ ~ js₂) (h₂₃ : Δ ⊨ js₂ ~ js₃) : Δ ⊨ js₁ ~ js₃ := by
  induction h₁₂ generalizing js₃
  case nil => exact h₂₃
  case cons h₁₂ ih =>
    cases h₂₃; case cons hjs h₂₃ =>
    refine .cons (ih hjs) (λ hvw ↦  ?_)
    exact ℰ.trans (h₁₂ hvw) (h₂₃ (𝒱.trans hvw.sym hvw))

/-* Semantic equivalence of values and computations *-/

@[simp] def semVal (Γ : Ctxt) (v w : Val) A := ∀ σ τ, Γ ⊨ σ ~ τ → (v⦃σ⦄, w⦃τ⦄) ∈ ⟦ A ⟧ᵛ
@[simp] def semCom (Γ : Ctxt) (Δ : Dtxt) (m n : Com) B := ∀ σ τ, Γ ⊨ σ ~ τ → ∀ js₁ js₂, Δ ⊨ js₁ ~ js₂ → (rejoin (m⦃σ⦄) js₁, rejoin (n⦃τ⦄) js₂) ∈ ⟦ B ⟧ᵉ
notation:40 Γ:41 "⊨" v:41 "~" w:41 "∶" A:41 => semVal Γ v w A
notation:40 Γ:41 "∣" Δ:41 "⊨" m:41 "~" n:41 "∶" B:41 => semCom Γ Δ m n B

/-* Semantic equivalence is a PER *-/

theorem semVal.sym {Γ v w} {A : ValType} (h : Γ ⊨ v ~ w ∶ A) : Γ ⊨ w ~ v ∶ A :=
  λ _ _ hστ ↦ (h _ _ hστ.sym).sym
theorem semCom.sym {Γ Δ m n} {B : ComType} (h : Γ ∣ Δ ⊨ m ~ n ∶ B) : Γ ∣ Δ ⊨ n ~ m ∶ B :=
  λ _ _ hστ _ _ hjs ↦  (h _ _ hστ.sym _ _ hjs.sym).sym

theorem semVal.trans {Γ v₁ v₂ v₃} {A : ValType} (h₁₂ : Γ ⊨ v₁ ~ v₂ ∶ A) (h₂₃ : Γ ⊨ v₂ ~ v₃ ∶ A) : Γ ⊨ v₁ ~ v₃ ∶ A :=
  λ _ _ hστ ↦ by refine 𝒱.trans (h₁₂ _ _ hστ) (h₂₃ _ _ (semCtxt.trans hστ.sym hστ))
theorem semCom.trans {Γ Δ m₁ m₂ m₃} {B : ComType} (h₁₂ : Γ ∣ Δ ⊨ m₁ ~ m₂ ∶ B) (h₂₃ : Γ ∣ Δ ⊨ m₂ ~ m₃ ∶ B) : Γ ∣ Δ ⊨ m₁ ~ m₃ ∶ B :=
  λ _ _ hστ _ _ hjs ↦ by refine ℰ.trans (h₁₂ _ _ hστ _ _ hjs) (h₂₃ _ _ (semCtxt.trans hστ.sym hστ) _ _ (semDtxt.trans hjs.sym hjs))

/-*---------------------------------------------
  Fundamental theorem of soundness
  of syntactic typing wrt semantic equivalence
---------------------------------------------*-/

theorem rejoinJump {Γ : Ctxt} {Δ js₁ js₂ j A B} (mem : Δ ∋ j ∶ A ↗ B) (h : Δ ⊨ js₁ ~ js₂) :
  ∀ {σ τ v w}, Γ ⊨ σ ~ τ → (v, w) ∈ ⟦ A ⟧ᵛ →
  (rejoin (jump j v) js₁, rejoin (jump j w) js₂) ∈ ⟦ B ⟧ᵉ := by
  induction h generalizing j A B
  case nil => cases mem
  case cons js₁ js₂ m n _ _ _ h _ =>
    cases mem
    case here =>
      intro σ τ v w hστ hvw; simp
      exact ℰ.bwd (.rejoin .γ) (.rejoin .γ) (h hvw)
    case there ih _ mem =>
      intro σ τ v w hστ hvw; simp
      exact .bwd (.rejoin .join't) (.rejoin .join't) (ih mem hστ hvw)

theorem soundness {Γ} :
  (∀ (v : Val) A, Γ ⊢ v ∶ A → Γ ⊨ v ~ v ∶ A) ∧
  (∀ {Δ} (m : Com) B, Γ ∣ Δ ⊢ m ∶ B → Γ ∣ Δ ⊨ m ~ m ∶ B) := by
  refine ⟨λ v A h ↦ ?val, λ m B h ↦ ?com⟩
  mutual_induction h, h
  all_goals intro σ τ hστ
  case var mem => exact hστ mem
  case unit => exact 𝒱.unit
  case inl ih => exact 𝒱.inl (ih σ τ hστ)
  case inr ih => exact 𝒱.inr (ih σ τ hστ)
  case thunk ih => exact 𝒱.thunk (ih σ τ hστ .nil .nil .nil)
  all_goals intro js₁ js₂ hjs
  case force ih =>
    simp [𝒱] at ih
    let ⟨_, _, h, em, en⟩ := ih σ τ hστ
    simp [em, en]; exact ℰ.bwdRejoin .π .π h
  case lam ih =>
    refine ℰ.bwdsRejoin .refl .refl (ℰ.lam (λ v w hA ↦ ?_))
    rw [substUnion, substUnion]
    exact ih (v +: σ) (w +: τ) (semCtxt.cons hA hστ) .nil .nil .nil
  case app ihm ihv =>
    let ⟨_ ,_, r₁, r₂, hAB⟩ := (ihm σ τ hστ .nil .nil .nil).lam_inv
    let hB := hAB _ _ (ihv σ τ hστ)
    exact ℰ.bwdsRejoin (.trans' (Evals.app r₁) (.once .β)) (.trans' (Evals.app r₂) (.once .β)) hB
  case ret ih => exact ℰ.bwdsRejoin .refl .refl (ℰ.ret (ih σ τ hστ))
  case letin ihm ihn =>
    let ⟨v, w, r₁, r₂, hA⟩ := (ihm σ τ hστ .nil .nil .nil).ret_inv
    refine ℰ.bwds ?_ ?_ (ihn (v +: σ) (w +: τ) (semCtxt.cons hA hστ) js₁ js₂ hjs)
    all_goals rw [← substUnion]
    . exact Evals.rejoin (.trans' (Evals.letin r₁) (.once .ζ))
    . exact Evals.rejoin (.trans' (Evals.letin r₂) (.once .ζ))
  case case ihv ihm ihn =>
    simp [𝒱] at ihv
    match ihv σ τ hστ with
    | .inl ⟨v, w, hA₁, ev, ew⟩ =>
      simp [ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm (v +: σ) (w +: τ) (semCtxt.cons hA₁ hστ) js₁ js₂ hjs)
      all_goals rw [← substUnion]; exact .rejoin .ιl
    | .inr ⟨v, w, hA₂, ev, ew⟩ =>
      simp [ev, ew]
      refine ℰ.bwd ?_ ?_ (ihn (v +: σ) (w +: τ) (semCtxt.cons hA₂ hστ) js₁ js₂ hjs)
      all_goals rw [← substUnion]; exact .rejoin .ιr
  case prod ihm ihn =>
    exact ℰ.bwdsRejoin .refl .refl (ℰ.prod (ihm σ τ hστ .nil .nil .nil) (ihn σ τ hστ .nil .nil .nil))
  case fst ih =>
    let ⟨_, _, _, _, r₁, r₂, hB₁⟩ := (ih σ τ hστ .nil .nil .nil).fst
    exact ℰ.bwdsRejoin (.trans' (Evals.fst r₁) (.once .π1)) (.trans' (Evals.fst r₂) (.once .π1)) hB₁
  case snd ih =>
    let ⟨_, _, _, _, r₁, r₂, hB₂⟩ := (ih σ τ hστ .nil .nil .nil).snd
    exact ℰ.bwdsRejoin (.trans' (Evals.snd r₁) (.once .π2)) (.trans' (Evals.snd r₂) (.once .π2)) hB₂
  case join m n _ _ _ _ ihm ihn =>
    let hn := ihn σ τ hστ (.cons (m⦃⇑ σ⦄) js₁) (.cons (m⦃⇑ τ⦄) js₂) (.cons hjs (λ {v w} hvw ↦ ?hm))
    case hm =>
      rw [substUnion, substUnion]
      exact ihm (v +: σ) (w +: τ) (semCtxt.cons hvw hστ) js₁ js₂ hjs
    exact hn
  case jump mem _ ihv => exact rejoinJump mem hjs hστ (ihv σ τ hστ)

def soundVal {Γ v} {A : ValType} : Γ ⊢ v ∶ A → Γ ⊨ v ~ v ∶ A := soundness.left v A
def soundCom {Γ Δ m} {B : ComType} : Γ ∣ Δ ⊢ m ∶ B → Γ ∣ Δ ⊨ m ~ m ∶ B := soundness.right m B
