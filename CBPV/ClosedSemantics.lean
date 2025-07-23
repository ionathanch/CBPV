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

/-* Semantic computations are normal and embed into semantic evaluations *-/

theorem 𝒞.nf {B m} (h : m ∈ ⟦ B ⟧ᶜ) : nf m :=
  match (generalizing := true) B with
  | F _ | Arr _ _ =>
    by unfold 𝒞 at h; let ⟨_, _, e⟩ := h; subst e; exact ⟨⟩
  | .Prod _ _ =>
    by unfold 𝒞 at h; let ⟨_, _, _, _, e⟩ := h; subst e; exact ⟨⟩

theorem 𝒞ℰ {B m} (h : m ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ :=
  by unfold ℰ; exact ⟨m, ⟨.refl, 𝒞.nf h⟩, h⟩

/-* Convenient constructors for the logical relation *-/

theorem 𝒱.unit : 𝒱 Unit unit := by simp [𝒱]
theorem 𝒱.inl {v A₁ A₂} (h : v ∈ ⟦A₁⟧ᵛ) : inl v ∈ ⟦Sum A₁ A₂⟧ᵛ := by simp [𝒱, h]
theorem 𝒱.inr {v A₁ A₂} (h : v ∈ ⟦A₂⟧ᵛ) : inr v ∈ ⟦Sum A₁ A₂⟧ᵛ := by simp [𝒱, h]
theorem 𝒱.thunk {m B} (h : m ∈ ⟦B⟧ᵉ) : thunk m ∈ ⟦U B⟧ᵛ := by simp [𝒱, h]
theorem ℰ.ret {v A} (h : v ∈ ⟦A⟧ᵛ) : ret v ∈ ⟦F A⟧ᵉ := by apply 𝒞ℰ; simp [𝒞, h]
theorem ℰ.lam {n A B} (h : ∀ v, v ∈ ⟦A⟧ᵛ → n⦃v⦄ ∈ ⟦B⟧ᵉ) : lam n ∈ ⟦Arr A B⟧ᵉ := by apply 𝒞ℰ; simp [𝒞]; exact h
theorem ℰ.prod {m n B₁ B₂} (hm : m ∈ ⟦B₁⟧ᵉ) (hn : n ∈ ⟦B₂⟧ᵉ) : prod m n ∈ ⟦Prod B₁ B₂⟧ᵉ := by apply 𝒞ℰ; simp [𝒞]; exact ⟨hm, hn⟩

/-* Semantic evaluations are backward closed under reduction *-/

theorem ℰ.bwds {B m n} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᵉ) : m ∈ ⟦ B ⟧ᵉ := by
  unfold ℰ at *
  let ⟨n', nn', h⟩ := h
  exact ⟨n', nn'.bwds r, h⟩

theorem ℰ.bwdsRejoin {B m n js} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᵉ) : rejoin m js ∈ ⟦ B ⟧ᵉ := by
  unfold ℰ at *
  let ⟨n', nn', h⟩ := h
  exact ⟨n', nn'.bwdsRejoin r, h⟩

theorem ℰ.bwd {B m n} (r : m ⇒ n) : n ∈ ⟦ B ⟧ᵉ → m ∈ ⟦ B ⟧ᵉ := ℰ.bwds (.once r)
theorem ℰ.bwdRejoin {B m n js} (r : m ⇒ n) : n ∈ ⟦ B ⟧ᵉ → rejoin m js ∈ ⟦ B ⟧ᵉ := ℰ.bwdsRejoin (.once r)

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
local notation:40 Γ:41 "∣" Δ:41 "⊨" js:41 => semDtxt Γ Δ js
inductive semDtxt (Γ : Ctxt) : Dtxt → J → Prop where
  | nil : Γ ∣ ⬝ ⊨ .nil
  | cons {Δ js m A B} : Γ ∣ Δ ⊨ js →
    (∀ {σ v}, Γ ⊨ σ → v ∈ ⟦ A ⟧ᵛ → (rejoin (m⦃v +: σ⦄) (substJ σ js)) ∈ ⟦ B ⟧ᵉ) →
    Γ ∣ Δ ∷ A ↗ B ⊨ .cons m js
end
notation:40 Γ:41 "∣" Δ:41 "⊨" js:41 => semDtxt Γ Δ js

theorem semDtxt.weaken {Γ Δ js A} (h : Γ ∣ Δ ⊨ js) : Γ ∷ A ∣ Δ ⊨ renameJ succ js := by
  induction h <;> constructor; assumption
  case cons m _ _ _ ih _ =>
    intro σ v hσ hv
    have e : (m⦃(v +: σ) ∘ lift succ⦄) = (m⦃v +: σ ∘ succ⦄) := by
      apply substComExt _ _ (λ n ↦ ?_); cases n <;> simp [lift]
    rw [substRenameCom, substRenameJ, e]
    exact ih (λ mem ↦ hσ (.there mem)) hv

/-* Semantic typing of values and computations *-/

@[simp] def semVal (Γ : Ctxt) v A := ∀ σ, Γ ⊨ σ → v⦃σ⦄ ∈ ⟦ A ⟧ᵛ
@[simp] def semCom (Γ : Ctxt) (Δ : Dtxt) m B := ∀ σ, Γ ⊨ σ → ∀ js, Γ ∣ Δ ⊨ js → rejoin (m⦃σ⦄) (substJ σ js) ∈ ⟦ B ⟧ᵉ
notation:40 Γ:41 "⊨" v:41 "∶" A:41 => semVal Γ v A
notation:40 Γ:41 "∣" Δ:41 "⊨" m:41 "∶" B:41 => semCom Γ Δ m B

/-*----------------------------------------
  Fundamental theorem of soundness
  of syntactic typing wrt semantic typing
----------------------------------------*-/

theorem rejoinJump {Γ Δ js j A B} (mem : Δ ∋ j ∶ A ↗ B) (h : Γ ∣ Δ ⊨ js) :
  ∀ {σ v}, Γ ⊨ σ → v ∈ ⟦ A ⟧ᵛ → (rejoin (jump j v) (substJ σ js)) ∈ ⟦ B ⟧ᵉ := by
  induction h generalizing j A B
  case nil => cases mem
  case cons h _ =>
    cases mem
    case here =>
      intro σ v hσ hv; simp
      refine .bwd (.rejoin ?_) (h hσ hv)
      rw [substUnion]; exact .γ
    case there ih _ mem =>
      intro σ v hσ hv; simp
      refine .bwd (.rejoin .join't) (ih mem hσ hv)

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
  case thunk ih => exact 𝒱.thunk (ih σ hσ .nil .nil)
  all_goals intro js hjs
  case force ih =>
    simp [𝒱] at ih
    let ⟨m, h, e⟩ := ih σ hσ
    simp; rw [e]
    exact ℰ.bwdRejoin .π h
  case lam ih =>
    refine ℰ.bwdsRejoin .refl (ℰ.lam (λ v hv ↦ ?_))
    rw [← substUnion]
    exact ih (v +: σ) (semCtxt.cons hv hσ) .nil .nil
  case app ihm ihv =>
    simp [ℰ] at ihm; simp [𝒞] at ihm
    let ⟨_, ⟨rlam, _⟩, n, h, e⟩ := ihm σ hσ .nil .nil; subst e
    exact ℰ.bwdsRejoin (.trans' (Evals.app rlam) (.once .β)) (h _ (ihv σ hσ))
  case ret ih => exact ℰ.bwdsRejoin .refl (ℰ.ret (ih σ hσ))
  case letin ihret ih =>
    simp [ℰ, 𝒞] at ihret
    let ⟨_, ⟨rret, _⟩, v, hv, e⟩ := ihret σ hσ .nil .nil; subst e
    let h := ih (v +: σ) (semCtxt.cons hv hσ) _ (.weaken hjs)
    rw [substUnion, substJDrop] at h
    exact ℰ.bwds (Evals.rejoin (.trans' (Evals.letin rret) (.once .ζ))) h
  case case ihv ihm ihn =>
    simp [𝒱] at ihv
    match ihv σ hσ with
    | .inl ⟨v, hv, e⟩ =>
      let hm := ihm (v +: σ) (semCtxt.cons hv hσ) _ (.weaken hjs)
      simp [e]; rw [substUnion, substJDrop] at hm
      exact ℰ.bwd (.rejoin .ιl) hm
    | .inr ⟨v, hv, e⟩ =>
      let hn := ihn (v +: σ) (semCtxt.cons hv hσ) _ (.weaken hjs)
      simp [e]; rw [substUnion, substJDrop] at hn
      exact ℰ.bwd (.rejoin .ιr) hn
  case prod ihm ihn =>
    exact ℰ.bwdsRejoin .refl (ℰ.prod (ihm σ hσ .nil .nil) (ihn σ hσ .nil .nil))
  case fst ih =>
    simp [ℰ] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, _⟩, n₁, n₂, hm, _, e⟩ := ih σ hσ .nil .nil; subst e
    exact ℰ.bwdsRejoin (.trans' (Evals.fst rprod) (.once .π1)) hm
  case snd ih =>
    simp [ℰ] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, nfprod⟩, n₁, n₂, _, hn, e⟩ := ih σ hσ .nil .nil; subst e
    exact ℰ.bwdsRejoin (.trans' (Evals.snd rprod) (.once .π2)) hn
  case join m _ _ _ _ _ ihm ihn =>
    let hn := ihn σ hσ (.cons m js) (.cons hjs (λ {σ v} hσ hv ↦ ?hm))
    case hm =>
      let hm := ihm (v +: σ) (semCtxt.cons hv hσ) _ (.weaken hjs)
      rw [substRenameJ, substJExt ((v +: σ) ∘ succ) σ (λ _ ↦ rfl)] at hm; exact hm
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
theorem normalization {m : Com} {B : ComType} (h : ⬝ ∣ ⬝ ⊢ m ∶ B) : SN m := by
  let ⟨_, soundCom⟩ := soundness (Γ := ⬝)
  let mB := soundCom m B h
  simp [ℰ] at mB
  let ⟨_, ⟨r, nfm⟩, _⟩ := mB var semCtxt.nil .nil .nil
  rw [substComId] at r
  exact r.sn nfm
