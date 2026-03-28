import CBPV.CCNF
import CBPV.Commutation
import CBPV.CK

open Nat ValType ComType Val Com

/-*--------------------------------------
  Semantic equivalence of continuations
--------------------------------------*-/

@[simp]
def semK (Γ : Ctxt) {δ} (Δ : Dtxt δ) k₁ k₂ B₁ B₂ :=
  ∀ {σ τ}, Γ ⊨ σ ~ τ →
  ∀ {φ ψ}, Δ ⊨ φ ~ ψ →
  ∀ {n₁ n₂}, (n₁, n₂) ∈ ⟦B₁⟧ᵉ →
  (rejoin ((substK σ k₁) [n₁]) φ, rejoin ((substK τ k₂) [n₂]) ψ) ∈ ⟦B₂⟧ᵉ
notation:40 Γ:41 "∣" Δ:41 "⊨" k₁:41 "~" k₂:41 "∶" B₁:41 "⇒" B₂:41 => semK Γ Δ k₁ k₂ B₁ B₂

namespace semK

theorem weaken {Γ δ} {Δ : Dtxt δ} {k₁ k₂ A B₁ B₂} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ∷ A ∣ Δ ⊨ renameK succ k₁ ~ renameK succ k₂ ∶ B₁ ⇒ B₂ := by
  intro σ τ hστ φ ψ hφψ n₁ n₂ hn
  rw [substRenameK, substRenameK]
  exact h (semCtxt.rename wRenameSucc hστ) hφψ hn

/-*--------------------------------------------------------------
  Fundamental theorem for semantic equivalence of continuations
--------------------------------------------------------------*-/

def nil {Γ δ B} {Δ : Dtxt δ} : Γ ∣ Δ ⊨ .nil ~ .nil ∶ B ⇒ B :=
  λ _ _ _ _ ↦ ℰ.bwdsRejoin .refl .refl

def fst {Γ δ} {Δ : Dtxt δ} {k₁ k₂ B₁ B₂ B₃} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₃) : Γ ∣ Δ ⊨ .fst k₁ ~ .fst k₂ ∶ Prod B₁ B₂ ⇒ B₃ := by
  intro σ τ hστ φ ψ hφψ n₁ n₂ hn; simp
  have ⟨n₁₁, n₁₂, n₂₁, n₂₂, rn₁, rn₂, hn₁⟩ := hn.fst
  refine ℰ.bwds ?left ?right (h hστ hφψ hn₁)
  all_goals refine .rejoin (.plug ?_)
  case left  => rw [← @weakenJCom0 n₁₁]; exact .trans' (Evals.fst rn₁) (.once .π1)
  case right => rw [← @weakenJCom0 n₂₁]; exact .trans' (Evals.fst rn₂) (.once .π1)

def snd {Γ δ} {Δ : Dtxt δ} {k₁ k₂ B₁ B₂ B₃} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₂ ⇒ B₃) : Γ ∣ Δ ⊨ .snd k₁ ~ .snd k₂ ∶ Prod B₁ B₂ ⇒ B₃ := by
  intro σ τ hστ φ ψ hφψ n₁ n₂ hn; simp
  have ⟨n₁₁, n₁₂, n₂₁, n₂₂, rn₁, rn₂, hn₂⟩ := hn.snd
  refine ℰ.bwds ?left ?right (h hστ hφψ hn₂)
  all_goals refine .rejoin (.plug ?_)
  case left  => rw [← @weakenJCom0 n₁₂]; exact .trans' (Evals.snd rn₁) (.once .π2)
  case right => rw [← @weakenJCom0 n₂₂]; exact .trans' (Evals.snd rn₂) (.once .π2)

theorem app {Γ δ} {Δ : Dtxt δ} {v w k₁ k₂ B₁ B₂} {A : ValType} (hA : Γ ⊨ v ~ w ∶ A) (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ∣ Δ ⊨ .app v k₁ ~ .app w k₂ ∶ Arr A B₁ ⇒ B₂ := by
  intro σ τ hστ φ ψ hφψ n₁ n₂ hn; simp
  have ⟨_, _, rn₁, rn₂, hm⟩ := hn.lam_inv
  refine ℰ.bwds ?left ?right (h hστ hφψ (hm _ _ (hA hστ)))
  all_goals refine .rejoin (.plug ?_)
  case left w _ => rw [← @weakenJCom0 (w⦃v⦃σ⦄⦄)]; exact .trans' (Evals.app rn₁) (.once .β)
  case right v  => rw [← @weakenJCom0 (v⦃w⦃τ⦄⦄)]; exact .trans' (Evals.app rn₂) (.once .β)

theorem letin {Γ δ} {Δ : Dtxt δ} {m₁ m₂ A} {B : ComType} (h : Γ ∷ A ∣ Δ ⊨ m₁ ~ m₂ ∶ B) : Γ ∣ Δ ⊨ .letin m₁ ~ .letin m₂ ∶ F A ⇒ B := by
  intro σ τ hστ φ ψ hφψ n₁ n₂ hn
  have ⟨v, w, rn₁, rn₂, hA⟩ := hn.ret_inv
  refine ℰ.bwds ?_ ?_ (h (semCtxt.cons hA hστ) hφψ)
  all_goals rw [← substUnion]; refine .rejoin ?_
  . exact .trans' (Evals.letin rn₁) (.once .ζ)
  . exact .trans' (Evals.letin rn₂) (.once .ζ)

end semK

theorem soundK {Γ δ} {Δ : Dtxt δ} {k B₁ B₂} (h : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) : Γ ∣ Δ ⊨ k ~ k ∶ B₁ ⇒ B₂ := by
  induction h
  case nil => exact semK.nil
  case app hv _ ih => exact semK.app (soundVal hv) ih
  case letin hm => exact semK.letin (soundCom hm)
  case fst ih => exact semK.fst ih
  case snd ih => exact semK.snd ih

/-*----------------------------------------------
  Semantic equivalence of plugged continuations
----------------------------------------------*-/

theorem semK.plug {Γ δ} {Δ : Dtxt δ} {n₁ n₂ k₁ k₂ B₁ B₂} (hk : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) (hn : Γ ∣ ⬝ ⊨ n₁ ~ n₂ ∶ B₁) : Γ ∣ Δ ⊨ (k₁[n₁]) ~ (k₂[n₂]) ∶ B₂ := by
  intro σ τ hστ φ ψ hφψ; rw [substPlug, substPlug]
  exact hk hστ hφψ (hn hστ .nil)

theorem semPlug {Γ δ} {Δ : Dtxt δ} {n₁ n₂ k B₁ B₂} (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (hn : Γ ∣ ⬝ ⊨ n₁ ~ n₂ ∶ B₁) : Γ ∣ Δ ⊨ (k [ n₁ ]) ~ (k [ n₂ ]) ∶ B₂ :=
  semK.plug (soundK hk) hn

/-*--------------------------------------
  Plugging commutes with configurations
--------------------------------------*-/

theorem semKletin {Γ δ} {Δ : Dtxt δ} {n m k B₁ B₂} (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ∣ ⬝ ⊢ letin n m ∶ B₁) :
  Γ ∣ Δ ⊨ (k [letin n m]) ~ letin n ((renameK succ k) [m]) ∶ B₂ := by
  induction hk generalizing n m
  case nil => exact soundCom (wtRenameJ (λ _ _ _ mem ↦ by cases mem) h)
  case app hv hk ih => exact semCom.trans (semPlug hk (appLet h hv)) (ih (wtLetApp h hv))
  case letin hm => exact letLet h hm
  case fst hk ih => exact semCom.trans (semPlug hk (fstLet h)) (ih (wtLetFst h))
  case snd hk ih => exact semCom.trans (semPlug hk (sndLet h)) (ih (wtLetSnd h))

theorem semKcase {Γ δ} {Δ : Dtxt δ} {v m₁ m₂ k B₁ B₂} (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ B₁) :
  Γ ∣ Δ ⊨ (k [case v m₁ m₂]) ~ case v ((renameK succ k) [m₁]) ((renameK succ k) [m₂]) ∶ B₂ := by
  induction hk generalizing v m₁ m₂
  case nil => exact soundCom (wtRenameJ (λ _ _ _ mem ↦ by cases mem) h)
  case app hv hk ih => exact semCom.trans (semPlug hk (appCase h hv)) (ih (wtCaseApp h hv))
  case letin hm => exact letCase h hm
  case fst hk ih => exact semCom.trans (semPlug hk (fstCase h)) (ih (wtCaseFst h))
  case snd hk ih => exact semCom.trans (semPlug hk (sndCase h)) (ih (wtCaseSnd h))

/-*---------------------------------------------
  Jumpification preserves semantic equivalence
---------------------------------------------*-/

theorem semKjoin {Γ δ} {Δ : Dtxt δ} {k k' m n B₁ B₂} (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (hn : Γ ∣ ⬝ ⊢ n ∶ B₁) (e : k.jumpify = .yes k' m) :
  Γ ∣ Δ ⊨ (k [ n ]) ~ join m (k' [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => cases e
  case letin hm =>
    simp at e; let ⟨ek, em⟩ := e; subst ek em
    intro σ τ hστ φ ψ hφψ
    let ⟨_, _, rn₁, rn₂, hA⟩ := (soundCom hn hστ .nil).ret_inv
    refine ℰ.bwds ?left ?right (soundCom hm (semCtxt.cons hA hστ) hφψ)
    all_goals refine .rejoin ?_; rw [← substUnion]
    case left => exact .trans' (Evals.letin rn₁) (.once .ζ)
    case right => exact .trans' (Evals.join (.trans' (Evals.letin rn₂) (.once .ζ))) (.once .γ)
  case app hv _ ih | fst ih | snd ih =>
    simp at e; split at e; cases e; injection e with ek em; subst ek em
    rename _ = _ => e
    refine ih ?_ e; constructor <;> assumption

theorem soundCCjoin {Γ δ δ'} {Δ : Dtxt δ} {Δ' : Dtxt δ'} {k k' m m' B₁ B₂} (le : δ' ≤ δ) (mj : m.joinless) (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (hm : Γ ∣ Δ' ⊢ m ∶ B₁) (e : k.jumpify = .yes k' m') :
  Γ ∣ Δ ⊨ ⟦m⟧ₘ k # le ~ join m' (⟦m⟧ₘ k' # .step le) ∶ B₂ := by
  mutual_induction hm generalizing δ Δ k k' m' mj
  all_goals intro σ τ
  -- impossible
  case join | jump => cases mj
  -- plugging cases
  case force hv => exact semKjoin hk (.force (.preservation mj hv)) e
  case lam hm _ => simp at mj; exact semKjoin hk (.lam (.preservation .refl mj .nil hm)) e
  case ret hv => exact semKjoin hk (.ret (.preservation mj hv)) e
  case prod hm₁ hm₂ _ _ =>
    let ⟨mj₁, mj₂⟩ := mj
    exact semKjoin hk (.prod (.preservation _ mj₁ .nil hm₁) (.preservation _ mj₂ .nil hm₂)) e
  -- extended continuation cases
  case app v _ _ _ hv ih =>
    let ⟨mj, vj⟩ := mj
    have goal := ih (k' := .app ⟦v⟧ᵥ k') (m' := m') (zero_le δ) mj (.app (.preservation vj hv) hk)
    simp only [K.jumpify, e] at goal; exact goal ⟨⟩
  case fst ih =>
    have goal := ih (k' := .fst k') (m' := m') (zero_le δ) mj (.fst hk)
    simp only [K.jumpify, e] at goal; exact goal ⟨⟩
  case snd ih =>
    have goal := ih (k' := .snd k') (m' := m') (zero_le δ) mj (.snd hk)
    simp only [K.jumpify, e] at goal; exact goal ⟨⟩
  -- configuration cases
  case letin Γ _ n m A _ hn hm ihn ihm =>
    intro hστ φ ψ hφψ; simp
    let ⟨nj, mj⟩ := mj
    have ⟨A', hk', hm'⟩ := wtK.jumpify hk e
    have ahm := ComWt.preservation le mj hk.weaken hm
    have ahm' := ComWt.preservation (.step le) mj (wtK.rename wRenameSucc hk') hm
    have ahn := ComWt.preservation (Δ := Δ ∷ A ↗ B₂) (zero_le (δ + 1)) nj (.letin (.jump .here (.var .here))) hn
    have aihm : Γ ∷ A ∣ Δ ⊨ (⟦ m ⟧ₘ renameK succ k # le) ~ join (renameCom (lift succ) m') (⟦ m ⟧ₘ renameK succ k' # .step le) ∶ B₂ :=
      λ {σ τ} ↦ ihm le mj hk.weaken (Jump.rename e) (σ := σ) (τ := τ)
    have hττ : Γ ⊨ τ ~ τ := semCtxt.trans hστ.sym hστ
    have hψ₂ : Δ ⊨ ψ ~ ψ := semDtxt.trans hφψ.sym hφψ
    apply ℰ.trans (ihn (zero_le δ) nj (wtK.letin ahm) rfl hστ hφψ)
    apply ℰ.trans (semCom.join aihm (soundCom ahn) hττ hψ₂)
    apply ℰ.trans (joinJoin hm' ahm' ahn hττ hψ₂); simp
    rw [← rejoin.eq_2 _ (m'⦃⇑ τ⦄), ← rejoin.eq_2 _ (m'⦃⇑ τ⦄)]
    rw [CCcom.renameJ (zero_le (δ + 1)) nj rfl]; simp
    apply ℰ.sym (ihn (zero_le (δ + 1)) nj (.letin ahm') rfl hττ
      (semDtxt.cons (m := m'⦃⇑ τ⦄) (n := m'⦃⇑ τ⦄) (B := B₂) hψ₂ (λ hvw ↦ ?_)))
    rw [substUnion, substUnion]
    exact soundCom hm' (semCtxt.cons hvw hττ) hψ₂
  case case hv hm₁ hm₂ ih₁ ih₂ =>
    intro hστ φ ψ hφψ; simp; rw [e]
    let ⟨vj, mj₁, mj₂⟩ := mj
    split; contradiction
    case _ eyes =>
      cases eyes
      let ⟨k'', e'⟩ := Jump.repeat e; rw [e']; simp
      have h₁ v w := ih₁ (σ := v +: σ) (τ := w +: τ) le mj₁ (wtK.weaken hk) (Jump.rename e)
      have h₂ v w := ih₂ (σ := v +: σ) (τ := w +: τ) le mj₂ (wtK.weaken hk) (Jump.rename e)
      let ihv := soundVal (ValWt.preservation vj hv) hστ
      unfold 𝒱 at ihv
      match ihv with
      | .inl ⟨v, w, hA, e₁, e₂⟩ =>
        rw [e₁, e₂]
        refine ℰ.bwd (.rejoin .ιl) (.rejoin (.join .ιl)) ?_
        rw [substUnion, substUnion]
        have hB₂ := h₁ v w (semCtxt.cons hA hστ) hφψ
        simp at hB₂; rw [renameUpSubstConsVal] at hB₂; exact hB₂
      | .inr ⟨v, w, hA, e₁, e₂⟩ =>
        rw [e₁, e₂]
        refine ℰ.bwd (.rejoin .ιr) (.rejoin (.join .ιr)) ?_
        rw [substUnion, substUnion]
        have hB₂ := h₂ v w (semCtxt.cons hA hστ) hφψ
        simp at hB₂; rw [renameUpSubstConsVal] at hB₂; exact hB₂
    case _ eyes =>
      cases eyes; split
      case _ eno =>
        let ⟨_, e⟩ := Jump.repeat e
        rw [e] at eno; cases eno
      case _ eyes =>
        let ⟨A', hk', hm'⟩ := wtK.jumpify hk e
        exact soundCom
          (.join hm' (.case (ValWt.preservation vj hv)
            (ComWt.preservation (.step le) mj₁ (wtK.weaken hk') hm₁)
            (ComWt.preservation (.step le) mj₂ (wtK.weaken hk') hm₂))) hστ hφψ
      case _ jumpn't eyes =>
        let ⟨_, e⟩ := Jump.repeat e
        rw [e] at eyes; cases eyes; cases jumpn't _ _ rfl

/-*------------------------------------------------------------
  Soundness of CC-normal translation wrt semantic equivalence
------------------------------------------------------------*-/

theorem soundCC {Γ} :
  (∀ {v} {A : ValType}, v.joinless → Γ ⊢ v ∶ A → Γ ⊨ v ~ ⟦v⟧ᵥ ∶ A) ∧
  (∀ {δ δ'} {Δ : Dtxt δ} {Δ' : Dtxt δ'} {m k₁ k₂} {B₁ B₂ : ComType} (eq : δ' = 0), m.joinless →
    Γ ∣ Δ' ⊢ m ∶ B₁ → Γ ∣ Δ ⊢ k₁ ∶ B₁ ⇒ B₂ → Γ ∣ Δ ⊢ k₂ ∶ B₁ ⇒ B₂ →
    Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂ → Γ ∣ Δ ⊨ (k₁[cast (congrArg Com eq) m]) ~ ⟦m⟧ₘ k₂ # cast (congrArg (· ≤ δ) eq.symm) (zero_le δ) ∶ B₂) := by
  refine ⟨λ vj h ↦ ?val, λ {δ δ' Δ Δ' m k₁ k₂ B₁ B₂} eq mj h wtk₁ wtk₂ hk ↦ ?com⟩
  mutual_induction h, h
  all_goals intro σ τ; try subst eq
  case force ih _ =>
    refine hk.plug (λ hστ φ ψ _ ↦ ?_)
    cases φ; cases ψ
    unfold semVal 𝒱 at ih
    let ⟨m, n, h, em, en⟩ := ih mj hστ; simp [em, en]
    refine ℰ.bwd .π .π ?_; simp [weakenJCom0, h]
  case lam ih _ =>
    refine hk.plug (λ hστ φ ψ _ ↦ ?_)
    cases φ; cases ψ
    refine ℰ.lam (λ v w hA ↦ ?_)
    rw [substUnion, substUnion]
    have goal := ih rfl mj .nil .nil (soundK .nil) (semCtxt.cons hA hστ) .nil
    simp [weakenJCom0] at goal; exact goal
  case app hv ihm ihv _ =>
    let ⟨mj, vj⟩ := mj
    exact ihm rfl mj (.app hv wtk₁) (.app (.preservation vj hv) wtk₂) (semK.app (ihv vj) hk)
  case ret ih _ =>
    refine hk.plug (λ hστ φ ψ _ ↦  ?_)
    cases φ; cases ψ
    exact ℰ.ret (ih mj hστ)
  case letin hn ihn Δ' _ hm ihm =>
    cases Δ'; let ⟨nj, mj⟩ := mj
    refine semCom.trans (semKletin wtk₁ (.letin hn hm)) ?_
    exact ihn rfl nj
      (.letin (wtk₁.weaken.plug hm))
      (.letin (.preservation (zero_le δ) mj wtk₂.weaken hm))
      (semK.letin (ihm rfl mj wtk₁.weaken wtk₂.weaken hk.weaken))
  case case Γ v A₁ A₂ B₁ hv ihv Δ' m n hm₁ hm₂ ihm₁ ihm₂ =>
    cases Δ'; let ⟨vj, mj₁, mj₂⟩ := mj
    refine semCom.trans (semKcase wtk₁ (.case hv hm₁ hm₂)) (λ hστ φ ψ hφψ ↦ ?_)
    unfold semVal 𝒱 at ihv
    match ihv vj hστ with
    | .inl ⟨v, w, hA₁, ev, ew⟩ =>
      have hB₂ := ihm₁ rfl mj₁ wtk₁.weaken wtk₂.weaken hk.weaken (semCtxt.cons hA₁ hστ) hφψ
      simp; split <;> simp [ev, ew]
      case _ | _ =>
        refine ℰ.bwd (.rejoin .ιl) (.rejoin .ιl) ?_
        rw [substUnion, substUnion]; exact hB₂
      case _ =>
        rename K _ => k'; rename Com _ => m'; rename _ = _ => e
        rw [← rejoin.eq_2]
        refine ℰ.bwd (.rejoin .ιl) (.rejoin .ιl) ?_
        rw [substUnion, substUnion]
        refine ℰ.trans hB₂ ?_
        have goal :=
          soundCCjoin (zero_le δ) mj₁ wtk₂.weaken hm₁ (Jump.rename e)
            (semCtxt.trans (semCtxt.sym (semCtxt.cons hA₁ hστ)) (semCtxt.cons hA₁ hστ))
            (semDtxt.trans (semDtxt.sym hφψ) hφψ)
        simp [renameUpSubstConsCom] at goal; exact goal
    | .inr ⟨v, w, hA₂, ev, ew⟩ =>
      have hB₂ := ihm₂ rfl mj₂ wtk₁.weaken wtk₂.weaken hk.weaken (semCtxt.cons hA₂ hστ) hφψ
      simp; split <;> simp [ev, ew]
      case _ | _ =>
        refine ℰ.bwd (.rejoin .ιr) (.rejoin .ιr) ?_
        rw [substUnion, substUnion]; exact hB₂
      case _ =>
        rename K _ => k'; rename Com _ => m'; rename _ = _ => e
        rw [← rejoin.eq_2]
        refine ℰ.bwd (.rejoin .ιr) (.rejoin .ιr) ?_
        rw [substUnion, substUnion]
        refine ℰ.trans hB₂ ?_
        have goal :=
          soundCCjoin (zero_le δ) mj₂ wtk₂.weaken hm₂ (Jump.rename e)
            (semCtxt.trans (semCtxt.sym (semCtxt.cons hA₂ hστ)) (semCtxt.cons hA₂ hστ))
            (semDtxt.trans (semDtxt.sym hφψ) hφψ)
        simp [renameUpSubstConsCom] at goal; exact goal
  case prod ihn₁ ihn₂ _ =>
    let ⟨nj₁, nj₂⟩ := mj
    refine hk.plug (λ hστ φ ψ _ ↦ ?_)
    cases φ; cases ψ; simp
    have hB₁ := ihn₁ rfl nj₁ .nil .nil (soundK .nil) hστ .nil
    have hB₂ := ihn₂ rfl nj₂ .nil .nil (soundK .nil) hστ .nil
    simp [weakenJCom0] at hB₁; simp [weakenJCom0] at hB₂
    exact ℰ.prod hB₁ hB₂
  case fst ih _ => exact ih rfl mj (.fst wtk₁) (.fst wtk₂) (semK.fst hk)
  case snd ih _ => exact ih rfl mj (.snd wtk₁) (.snd wtk₂) (semK.snd hk)
  case join | jump => cases mj
  all_goals intro hστ
  case var mem => exact hστ mem
  case unit => exact 𝒱.unit
  case inl ih => exact 𝒱.inl (ih vj hστ)
  case inr ih => exact 𝒱.inr (ih vj hστ)
  case thunk ih =>
    have goal := ih rfl vj .nil .nil (soundK .nil) hστ .nil
    simp [weakenJCom0] at goal; exact 𝒱.thunk goal

theorem soundCCnil {Γ m B} (mj : m.joinless) (h : Γ ∣ ⬝ ⊢ m ∶ B) : Γ ∣ ⬝ ⊨ m ~ ⟦m⟧ₘ ∶ B := by
  intro σ τ hστ φ ψ hφψ
  have goal := soundCC.right rfl mj h .nil .nil semK.nil hστ hφψ
  simp at goal; rw [weakenJCom0] at goal; exact goal

/-*-------------------------------------------------------------
  CC-normalized ground returners compute the same normal forms
-------------------------------------------------------------*-/

@[simp]
def isGround : ValType → Prop
  | .Unit => True
  | .Sum A₁ A₂ => isGround A₁ ∧ isGround A₂
  | U _ => False

theorem 𝒱.ground {v w A} (h : (v, w) ∈ ⟦A⟧ᵛ) (g : isGround A) : v = w := by
  mutual_induction A generalizing v w g
  all_goals unfold 𝒱 at h
  case Unit => simp [h]
  case Sum ihA₁ ihA₂ =>
    match h with
    | .inl ⟨_, _, hA₁, ev, ew⟩ => subst ev ew; simp; exact ihA₁ hA₁ g.left
    | .inr ⟨_, _, hA₂, ev, ew⟩ => subst ev ew; simp; exact ihA₂ hA₂ g.right
  case U => simp at g

theorem retGround {m v A} (mj : m.joinless) (h : ⬝ ∣ ⬝ ⊢ m ∶ F A) (g : isGround A) (nm : m ⇓ₙ ret v) : ⟦m⟧ₘ ⇓ₙ ret v := by
  let ⟨r, nfm⟩ := nm
  let hm := soundCCnil mj h semCtxt.nil .nil
  rw [substComId, substComId] at hm
  unfold ℰ 𝒞 at hm
  let ⟨_, _, ⟨r', _⟩, ⟨ra', _⟩, ⟨v₁, v₂, hA, eret₁, eret₂⟩⟩ := hm
  subst eret₁ eret₂; simp at r' ra'
  rw [← hA.ground g] at ra'
  rw [← (r'.merge nm).ret_inv]
  exact ⟨ra', nfm⟩

theorem retGroundVal {m A} (mj : m.joinless) (h : ⬝ ∣ ⬝ ⊢ m ∶ F A) (g : isGround A) : ∃ v, m ⇒⋆ ret v ∧ ⟦m⟧ₘ ⇒⋆ ret v := by
  let ⟨n, ⟨r, nfm⟩⟩ := safety h
  let hm := soundCCnil mj h semCtxt.nil .nil
  rw [substComId, substComId] at hm
  unfold ℰ 𝒞 at hm
  let ⟨_, _, ⟨r', _⟩, ⟨ra', _⟩, ⟨v, _, hA, eret₁, eret₂⟩⟩ := hm
  subst eret₁ eret₂; simp at r' ra'
  rw [← hA.ground g] at ra'; exists v

theorem retGroundCK {m v A} (mj : m.joinless) (h : ⬝ ∣ ⬝ ⊢ m ∶ F A) (g : isGround A)
  (r : ⟨0, m, .nil⟩ ⤳⋆ ⟨0, ret v, .nil⟩) : ⟨0, ⟦m⟧ₘ, .nil⟩ ⤳⋆ ⟨0, ret v, .nil⟩ :=
  evalStep ⟨⟩ (retGround mj h g ⟨stepEvalsNil r, ⟨⟩⟩).left
