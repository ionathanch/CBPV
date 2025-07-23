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

-- Convenient constructors for the logical relation
theorem 𝒱.unit : 𝒱 Unit unit := by simp [𝒱]
theorem 𝒱.inl {v A₁ A₂} (h : 𝒱 A₁ v) : 𝒱 (Sum A₁ A₂) (inl v) := by simp [𝒱]; assumption
theorem 𝒱.inr {v A₁ A₂} (h : 𝒱 A₂ v) : 𝒱 (Sum A₁ A₂) (inr v) := by simp [𝒱]; assumption
theorem 𝒱.thunk {m B} (h : ℰ B m) : 𝒱 (U B) (thunk m) := by simp [𝒱]; assumption
theorem 𝒞.ret {v A} (h : 𝒱 A v) : 𝒞 (F A) (ret v) := by simp [𝒞]; assumption
theorem 𝒞.lam {n A B} (h : ∀ v, 𝒱 A v → ℰ B (n⦃v⦄)) : 𝒞 (Arr A B) (lam n) := by simp [𝒞]; assumption
theorem 𝒞.prod {m n B₁ B₂} (hm : ℰ B₁ m) (hn : ℰ B₂ n) : 𝒞 (Prod B₁ B₂) (prod m n) := by simp [𝒞]; constructor <;> assumption

-- Semantic computations are normal
theorem 𝒞.nf {B m} (h : m ∈ ⟦ B ⟧ᶜ) : nf m :=
  match (generalizing := true) B with
  | F _ | Arr _ _ =>
    by unfold 𝒞 at h; let ⟨_, _, e⟩ := h; subst e; exact ⟨⟩
  | .Prod _ _ =>
    by unfold 𝒞 at h; let ⟨_, _, _, _, e⟩ := h; subst e; exact ⟨⟩

-- Semantic computations embed into semantic evaluations
theorem 𝒞ℰ {B m} (h : m ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ :=
  by unfold ℰ; exact ⟨m, ⟨.refl, 𝒞.nf h⟩, h⟩

-- Semantic evaluations are backward closed under reduction
theorem ℰ.bwd {B m n} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᵉ) : m ∈ ⟦ B ⟧ᵉ := by
  unfold ℰ at *
  let ⟨n', ⟨r', nfn⟩, h⟩ := h
  refine ⟨n', ⟨.trans' r r', nfn⟩, h⟩
theorem 𝒞.bwd {B m n} (r : m ⇒⋆ n) (h : n ∈ ⟦ B ⟧ᶜ) : m ∈ ⟦ B ⟧ᵉ := ℰ.bwd r (𝒞ℰ h)

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
      refine .bwd (.rejoinCong (.once ?_)) (h hσ hv)
      rw [substUnion]; exact .γ
    case there ih _ mem =>
      intro σ v hσ hv; simp
      refine .bwd (.rejoinCong (.once .join't)) (ih mem hσ hv)

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
    let hm := ih σ hσ .nil .nil
    exact 𝒱.thunk hm
  all_goals intro js hjs
  case force ih =>
    simp [𝒱, ℰ] at ih
    let ⟨m, ⟨n, ⟨r, nfn⟩, h⟩, e⟩ := ih σ hσ
    simp; rw [e]
    refine 𝒞.bwd ?_ h
    calc rejoin (force (thunk m)) (substJ σ js)
      _ ⇒  rejoin m (substJ σ js) := .rejoinCong .π
      _ ⇒⋆ rejoin n (substJ σ js) := .rejoinCong r
      _ ⇒⋆ n                     := nfn.rejoinDrop
  case lam ih =>
    refine 𝒞.bwd (nf.rejoinDrop ⟨⟩) (𝒞.lam (λ v hv ↦ ?_))
    rw [← substUnion]
    exact ih (v +: σ) (semCtxt.cons hv hσ) .nil .nil
  case app m v _ _ _ _ ihm ihv =>
    simp [ℰ, 𝒞] at ihm
    let ⟨_, ⟨rlam, _⟩, n, h, e⟩ := ihm σ hσ .nil .nil; subst e
    let ⟨nv, ⟨rval, nfnv⟩, h⟩ := h _ (ihv σ hσ)
    refine 𝒞.bwd ?_ h
    calc rejoin (app (m⦃σ⦄) (v⦃σ⦄)) (substJ σ js)
      _ ⇒⋆ rejoin (app (lam n) (v⦃σ⦄)) (substJ σ js) := .rejoinCong (.app rlam)
      _ ⇒  rejoin (n⦃v⦃σ⦄⦄) (substJ σ js)            := .rejoinCong .β
      _ ⇒⋆ rejoin nv (substJ σ js)                   := .rejoinCong rval
      _ ⇒⋆ nv                                        := nfnv.rejoinDrop
  case ret ih => exact 𝒞.bwd (nf.rejoinDrop ⟨⟩) (𝒞.ret (ih σ hσ))
  case letin m n _ _ _ _ ihret ih =>
    simp [ℰ, 𝒞] at ihret ih
    let ⟨_, ⟨rret, _⟩, v, hv, e⟩ := ihret σ hσ .nil .nil; subst e
    let ⟨nv, ⟨rlet, nflet⟩, h⟩ := ih (v +: σ) (semCtxt.cons hv hσ) _ (.weaken hjs)
    rw [substUnion, substJDrop] at rlet
    refine 𝒞.bwd ?_ h
    calc rejoin (letin (m⦃σ⦄) (n⦃⇑ σ⦄)) (substJ σ js)
      _ ⇒⋆ rejoin (letin (ret v) (n⦃⇑ σ⦄)) (substJ σ js) := .rejoinCong (.letin rret)
      _ ⇒  rejoin (n⦃⇑ σ⦄⦃v⦄) (substJ σ js)              := .rejoinCong .ζ
      _ ⇒⋆ nv                                            := rlet
  case case m n _ _ _ _ _ _ ihv ihm ihn =>
    simp [𝒱] at ihv
    match ihv σ hσ with
    | .inl ⟨v, hv, e⟩ =>
      let hm := ihm (v +: σ) (semCtxt.cons hv hσ) _ (.weaken hjs)
      simp [e]; rw [substUnion, substJDrop] at hm
      exact ℰ.bwd (.rejoinCong (.once .ιl)) hm
    | .inr ⟨v, hv, e⟩ =>
      let hn := ihn (v +: σ) (semCtxt.cons hv hσ) _ (.weaken hjs)
      simp [e]; rw [substUnion, substJDrop] at hn
      exact ℰ.bwd (.rejoinCong (.once .ιr)) hn
  case prod m n _ _ _ _ ihm ihn =>
    simp [ℰ, 𝒞] at ihm ihn
    let ⟨_, ⟨rm, _⟩, hm⟩ := ihm σ hσ .nil .nil
    let ⟨_, ⟨rn, _⟩, hn⟩ := ihn σ hσ .nil .nil
    simp at rm rn
    exact 𝒞.bwd (nf.rejoinDrop ⟨⟩) (𝒞.prod (𝒞.bwd rm hm) (𝒞.bwd rn hn))
  case fst m _ _ _ ih =>
    simp [ℰ] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, _⟩, n₁, n₂, hm, _, e⟩ := ih σ hσ .nil .nil
    subst e; simp at rprod; unfold ℰ at hm
    let ⟨n₁', ⟨r', nfn⟩, hm⟩ := hm
    refine 𝒞.bwd ?_ hm
    calc rejoin (fst (m⦃σ⦄)) (substJ σ js)
      _ ⇒⋆ rejoin (fst (prod n₁ n₂)) (substJ σ js) := .rejoinCong (.fst rprod)
      _ ⇒  rejoin n₁ (substJ σ js)                 := .rejoinCong .π1
      _ ⇒⋆ rejoin n₁' (substJ σ js)                := .rejoinCong r'
      _ ⇒⋆ n₁'                                     := nfn.rejoinDrop
  case snd m _ _ _ ih =>
    simp [ℰ] at ih; unfold 𝒞 at ih
    let ⟨_, ⟨rprod, nfprod⟩, n₁, n₂, _, hn, e⟩ := ih σ hσ .nil .nil
    subst e; simp at rprod; unfold ℰ at hn
    let ⟨n₂', ⟨r', nfn⟩, hn⟩ := hn
    refine 𝒞.bwd ?_ hn
    calc rejoin (snd (m⦃σ⦄)) (substJ σ js)
      _ ⇒⋆ rejoin (snd (prod n₁ n₂)) (substJ σ js) := .rejoinCong (.snd rprod)
      _ ⇒  rejoin n₂ (substJ σ js)                 := .rejoinCong .π2
      _ ⇒⋆ rejoin n₂' (substJ σ js)                := .rejoinCong r'
      _ ⇒⋆ n₂'                                     := nfn.rejoinDrop
  case join Γ Δ m n A B _ _ ihm ihn =>
    simp [ℰ] at ihn
    let ⟨n', ⟨r, _⟩, hn⟩ := ihn σ hσ (.cons m js) (.cons hjs (λ {σ v} hσ hv ↦ ?hm))
    case hm =>
      let hm := ihm (v +: σ) (semCtxt.cons hv hσ) _ (.weaken hjs)
      rw [substRenameJ, substJExt ((v +: σ) ∘ succ) σ (λ _ ↦ rfl)] at hm; exact hm
    exact 𝒞.bwd r hn
  case jump j v _ _ mem _ ihv => exact rejoinJump mem hjs hσ (ihv σ hσ)

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
