import CBPV.Equivalence

open Nat ValType ComType Val Com

theorem letLet {Γ δ} {Δ : Dtxt δ} {A n m m'} {B : ComType}
  (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ F A)
  (hm' : Γ ∷ A ∣ Δ ⊢ m' ∶ B) :
  Γ ∣ Δ ⊨ letin (letin n m) m' ~ letin n (letin m (renameCom (lift succ) m')) ∶ B := by
  intro σ τ hστ φ ψ hφψ
  let ⟨v₁, v₂, rv₁, rv₂, hA⟩ := (soundCom hlet hστ .nil).ret_inv
  have r₁' : letin ((letin n m)⦃σ⦄) (m'⦃⇑ σ⦄) ⇒⋆ m'⦃v₁ +: σ⦄ := by
    rw [← substUnion]; exact .trans' rv₁.letin (.once .ζ)
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, rw₁, rw₂, _⟩ := (soundCom hn hστ .nil).ret_inv
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ m⦃w₂ +: τ⦄ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.letin
    _ ⇒  m⦃w₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
  have r₂' : (letin n (letin m (renameCom (lift succ) m')))⦃τ⦄ ⇒⋆ m'⦃v₂ +: τ⦄ := calc
    _ ⇒⋆ letin (ret w₂) (letin (m⦃⇑ τ⦄) ((renameCom (lift succ) m')⦃⇑⇑ τ⦄))
      := by simp only [substCom]; exact rw₂.letin
    _ ⇒ (letin (m⦃⇑ τ⦄) ((renameCom (lift succ) m')⦃⇑⇑ τ⦄))⦃w₂⦄ := .ζ
    _ = letin (m⦃w₂ +: τ⦄) (m'⦃⇑τ⦄)
      := by simp only [substCom]; rw [substUnion, renameDropSubst]
    _ ⇒⋆ letin (ret v₂) (m'⦃⇑τ⦄) := .letin (rlet.merge ⟨rv₂, ⟨⟩⟩)
    _ ⇒ m'⦃v₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
  have goal := soundCom hm' (semCtxt.cons hA hστ) hφψ
  exact ℰ.bwds (.rejoin r₁') (.rejoin r₂') goal

theorem appLet {Γ δ} {Δ : Dtxt δ} {n m v A B}
  (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Arr A B)
  (hv : Γ ⊢ v ∶ A) :
  Γ ∣ Δ ⊨ app (letin n m) v ~ letin n (app m (renameVal succ v)) ∶ B := by
  intro σ τ hστ φ ψ hφψ
  let ⟨n₁, n₂, r₁, r₂, hB⟩ := (soundCom hlet hστ .nil).lam_inv
  have r₁' : app ((letin n m)⦃σ⦄) (v⦃σ⦄) ⇒⋆ n₁⦃v⦃σ⦄⦄ := by
    rw [← @weakenJCom0 (n₁⦃v⦃σ⦄⦄)]; exact .trans' r₁.app (.once .β)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn hστ .nil).ret_inv
  let ⟨_, m₂, _, rm₂, _⟩ := (soundCom hm (semCtxt.cons hA' hστ) .nil).lam_inv
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ lam m₂ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.letin
    _ ⇒  m⦃w₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
    _ ⇒⋆ lam m₂ := rm₂
  injection (r₂.merge ⟨rlet, ⟨⟩⟩).lam_inv with _ e; subst e
  have r₂' : letin (n⦃τ⦄) (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄))
      ⇒⋆ n₂⦃v⦃τ⦄⦄ := calc
    _ ⇒⋆ letin (ret w₂) (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄)) := rw₂.letin
    _ ⇒  (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄))⦃w₂⦄ := .ζ
    _ = app (m⦃w₂ +: τ⦄) (v⦃τ⦄)
      := by simp only [substCom]; rw [substUnion, renameUpSubstVal, substDropVal]
    _ ⇒⋆ app (lam n₂) (v⦃τ⦄) := rm₂.app
    _ ⇒  weakenJCom 0 (n₂⦃v⦃τ⦄⦄) := .β
    _ ⇒⋆ n₂⦃v⦃τ⦄⦄ := by rw [weakenJCom0]
  exact ℰ.bwdsRejoin r₁' r₂' (hB _ _ (soundVal hv hστ))

theorem fstLet {Γ δ} {Δ : Dtxt δ} {n m B₁ B₂}
  (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊨ fst (letin n m) ~ letin n (fst m) ∶ B₁ := by
  intro σ τ hστ φ ψ hφψ
  let ⟨n₁, _, n₂, _, r₁, r₂, hB₁⟩ := (soundCom hlet hστ .nil).fst
  have r₁' : fst ((letin n m)⦃σ⦄) ⇒⋆ n₁ := by
    rw [← @weakenJCom0 n₁]; exact .trans' r₁.fst (.once .π1)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn hστ .nil).ret_inv
  let ⟨m₁, _, m₂, _, _, r₂', _⟩ := (soundCom hm (semCtxt.cons hA' hστ) .nil).fst
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ prod m₂ _ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.letin
    _ ⇒  m⦃w₂ +: τ⦄              := by rw [← substUnion]; exact .ζ
    _ ⇒⋆ prod m₂ _               := r₂'
  injection (r₂.merge ⟨rlet, ⟨⟩⟩).prod_inv with _ e₂ e₂; subst e₂ e₂
  have r₂' : letin (n⦃τ⦄) (fst (m⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
    _ ⇒⋆ letin (ret w₂) (fst (m⦃⇑ τ⦄)) := rw₂.letin
    _ ⇒  fst (m⦃⇑ τ⦄⦃w₂⦄)              := .ζ
    _ =  fst (m⦃w₂ +: τ⦄)              := by rw [substUnion]
    _ ⇒⋆ fst (prod n₂ _)               := r₂'.fst
    _ ⇒  weakenJCom 0 n₂               := .π1
    _ ⇒⋆ n₂                            := by rw [weakenJCom0]
  exact ℰ.bwdsRejoin r₁' r₂' hB₁

theorem sndLet {Γ δ} {Δ : Dtxt δ} {n m B₁ B₂}
  (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊨ snd (letin n m) ~ letin n (snd m) ∶ B₂ := by
  intro σ τ hστ φ ψ hφψ
  let ⟨_, n₁, _, n₂, r₁, r₂, hB₂⟩ := (soundCom hlet hστ .nil).snd
  have r₁' : snd ((letin n m)⦃σ⦄) ⇒⋆ n₁ := by
    rw [← @weakenJCom0 n₁]; exact .trans' r₁.snd (.once .π2)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn hστ .nil).ret_inv
  let ⟨m₁, _, m₂, _, _, r₂', _⟩ := (soundCom hm (semCtxt.cons hA' hστ) .nil).fst
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ prod m₂ _ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.letin
    _ ⇒  m⦃w₂ +: τ⦄              := by rw [← substUnion]; exact .ζ
    _ ⇒⋆ prod m₂ _               := r₂'
  injection (r₂.merge ⟨rlet, ⟨⟩⟩).prod_inv with _ e₂ e₂; subst e₂ e₂
  have r₂' : letin (n⦃τ⦄) (snd (m⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
    _ ⇒⋆ letin (ret w₂) (snd (m⦃⇑ τ⦄)) := rw₂.letin
    _ ⇒  snd (m⦃⇑ τ⦄⦃w₂⦄)              := .ζ
    _ =  snd (m⦃w₂ +: τ⦄)              := by rw [substUnion]
    _ ⇒⋆ snd (prod _ n₂)               := r₂'.snd
    _ ⇒  weakenJCom 0 n₂               := .π2
    _ ⇒⋆ n₂                            := by rw [weakenJCom0]
  exact ℰ.bwdsRejoin r₁' r₂' hB₂

theorem letCase {Γ δ} {Δ : Dtxt δ} {v m₁ m₂ n A} {B : ComType}
  (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ F A)
  (hn : Γ ∷ A ∣ Δ ⊢ n ∶ B) :
  Γ ∣ Δ ⊨ letin (case v m₁ m₂) n
    ~ case v (letin m₁ (renameCom (lift succ) n)) (letin m₂ (renameCom (lift succ) n)) ∶ B := by
  intro σ τ hστ φ ψ hφψ
  let ⟨v₁, v₂, rv₁, rv₂, hA⟩ := (soundCom hcase hστ .nil).ret_inv
  have r₁' : letin ((case v m₁ m₂)⦃σ⦄) (n⦃⇑ σ⦄) ⇒⋆ n⦃v₁ +: σ⦄ := by
    rw [← substUnion]; exact .trans' rv₁.letin (.once .ζ)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨w₁, w₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at rv₂
    let ⟨u₁, u₂, ru₁, ru₂, _⟩ := (soundCom hm₁ (semCtxt.cons hA₁ hστ) .nil).ret_inv
    let rcase : case (inl w₂) (m₁⦃⇑ τ⦄) (m₂⦃⇑ τ⦄) ⇒⋆ ret u₂ := calc
      _ ⇒ m₁⦃w₂ +: τ⦄ := by rw [← substUnion]; exact .ιl
      _ ⇒⋆ ret u₂     := ru₂
    injection (rv₂.merge ⟨rcase, ⟨⟩⟩).ret_inv with _ e; subst e
    have r₂' : case (inl w₂)
                    (letin (m₁⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))
                    (letin (m₂⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))
               ⇒⋆ n⦃v₂ +: τ⦄ := calc
        _ ⇒ (letin (m₁⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))⦃w₂⦄ := .ιl
        _ ⇒⋆ letin (m₁⦃w₂ +: τ⦄) (n⦃⇑τ⦄)
          := by simp only [substCom]; rw [substUnion, renameDropSubst]
        _ ⇒⋆ letin (ret v₂) (n⦃⇑ τ⦄) := ru₂.letin
        _ ⇒ n⦃v₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
    have goal := soundCom hn (semCtxt.cons hA hστ) hφψ
    exact ℰ.bwds (.rejoin r₁') (.rejoin r₂') goal
  | .inr ⟨w₁, w₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at rv₂
    let ⟨u₁, u₂, ru₁, ru₂, _⟩ := (soundCom hm₂ (semCtxt.cons hA₂ hστ) .nil).ret_inv
    let rcase : case (inr w₂) (m₁⦃⇑ τ⦄) (m₂⦃⇑ τ⦄) ⇒⋆ ret u₂ := calc
      _ ⇒ m₂⦃w₂ +: τ⦄ := by rw [← substUnion]; exact .ιr
      _ ⇒⋆ ret u₂     := ru₂
    injection (rv₂.merge ⟨rcase, ⟨⟩⟩).ret_inv with _ e; subst e
    have r₂' : case (inr w₂)
                    (letin (m₁⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))
                    (letin (m₂⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))
               ⇒⋆ n⦃v₂ +: τ⦄ := calc
        _ ⇒ (letin (m₂⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))⦃w₂⦄ := .ιr
        _ ⇒⋆ letin (m₂⦃w₂ +: τ⦄) (n⦃⇑τ⦄)
          := by simp only [substCom]; rw [substUnion, renameDropSubst]
        _ ⇒⋆ letin (ret v₂) (n⦃⇑ τ⦄) := ru₂.letin
        _ ⇒ n⦃v₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
    have goal := soundCom hn (semCtxt.cons hA hστ) hφψ
    exact ℰ.bwds (.rejoin r₁') (.rejoin r₂') goal

theorem appCase {Γ δ} {Δ : Dtxt δ} {v w m₁ m₂ A B}
  (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Arr A B)
  (hw : Γ ⊢ w ∶ A) :
  Γ ∣ Δ ⊨ app (case v m₁ m₂) w ~ case v (app m₁ (renameVal succ w)) (app m₂ (renameVal succ w)) ∶ B := by
  intro σ τ hστ φ ψ hφψ
  let ⟨n₁, n₂, r₁, r₂, hB₁⟩ := (soundCom hcase hστ .nil).lam_inv
  have r₁' : app ((case v m₁ m₂)⦃σ⦄) (w⦃σ⦄) ⇒⋆ n₁⦃w⦃σ⦄⦄ := by
    rw [← @weakenJCom0 (n₁⦃w⦃σ⦄⦄)]; exact .trans' r₁.app (.once .β)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, r₂', _⟩ := (soundCom hm₁ (semCtxt.cons hA₁ hστ) .nil).lam_inv
    have r' := Evals.merge (RTC.once .ιl) ⟨r₂, ⟨⟩⟩; rw [substUnion] at r'
    have r' := Evals.merge r' ⟨r₂', ⟨⟩⟩
    injection r'.lam_inv with _ en₂; subst en₂
    have r₂' :
      case (.inl v₂) (app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄)) (app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄))
        ⇒⋆ n₂⦃w⦃τ⦄⦄ := calc
      _ ⇒  app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄) ⦃v₂⦄ := .ιl
      _ =  app (m₁⦃v₂ +: τ⦄) (w⦃τ⦄)
        := by simp only [substCom]; rw [substUnion, renameUpSubstVal, substDropVal]
      _ ⇒⋆ app (lam n₂) (w⦃τ⦄)     := r₂'.app
      _ ⇒  weakenJCom 0 (n₂⦃w⦃τ⦄⦄) := .β
      _ ⇒⋆ n₂⦃w⦃τ⦄⦄                := by rw [weakenJCom0]
    exact ℰ.bwdsRejoin r₁' r₂' (hB₁ _ _ (soundVal hw hστ))
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, r₂', _⟩ := (soundCom hm₂ (semCtxt.cons hA₂ hστ) .nil).lam_inv
    have r' := Evals.merge (RTC.once .ιr) ⟨r₂, ⟨⟩⟩; rw [substUnion] at r'
    have r' := Evals.merge r' ⟨r₂', ⟨⟩⟩
    injection r'.lam_inv with _ en₂; subst en₂
    have r₂' :
      case (.inr v₂) (app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄)) (app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄))
        ⇒⋆ n₂⦃w⦃τ⦄⦄ := calc
      _ ⇒  app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄) ⦃v₂⦄ := .ιr
      _ =  app (m₂⦃v₂ +: τ⦄) (w⦃τ⦄)
        := by simp only [substCom]; rw [substUnion, renameUpSubstVal, substDropVal]
      _ ⇒⋆ app (lam n₂) (w⦃τ⦄)     := r₂'.app
      _ ⇒  weakenJCom 0 (n₂⦃w⦃τ⦄⦄) := .β
      _ ⇒⋆ n₂⦃w⦃τ⦄⦄                := by rw [weakenJCom0]
    exact ℰ.bwdsRejoin r₁' r₂' (hB₁ _ _ (soundVal hw hστ))

theorem fstCase {Γ δ} {Δ : Dtxt δ} {v m₁ m₂ B₁ B₂}
  (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊨ fst (case v m₁ m₂) ~ case v (fst m₁) (fst m₂) ∶ B₁ := by
  intro σ τ hστ φ ψ hφψ
  let ⟨n₁, _, n₂, _, r₁, r₂, hB₁⟩ := (soundCom hcase hστ .nil).fst
  have r₁' : fst ((case v m₁ m₂)⦃σ⦄) ⇒⋆ n₁ := by
    rw [← @weakenJCom0 n₁]; exact .trans' r₁.fst (.once .π1)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₁ (semCtxt.cons hA₁ hστ) .nil).fst
    have r' := Evals.merge (RTC.once .ιl) ⟨r₂, ⟨⟩⟩; rw [substUnion] at r'
    have r' := Evals.merge r' ⟨r₂', ⟨⟩⟩
    injection r'.prod_inv with _ en₁ en₂; subst en₁ en₂
    have r₂' :
      case (inl v₂) (fst (m₁⦃⇑ τ⦄)) (fst (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  fst (m₁⦃⇑ τ⦄)⦃v₂⦄ := .ιl
      _ =  fst (m₁⦃v₂ +: τ⦄) := by simp only [substCom]; rw [substUnion]
      _ ⇒⋆ fst (prod n₂ _)   := r₂'.fst
      _ ⇒  weakenJCom 0 n₂   := .π1
      _ ⇒⋆ n₂                := by rw [weakenJCom0]
    exact ℰ.bwdsRejoin r₁' r₂' hB₁
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₂ (semCtxt.cons hA₂ hστ) .nil).fst
    have r' := Evals.merge (RTC.once .ιr) ⟨r₂, ⟨⟩⟩; rw [substUnion] at r'
    have r' := Evals.merge r' ⟨r₂', ⟨⟩⟩
    injection r'.prod_inv with _ en₁ en₂; subst en₁ en₂
    have r₂' :
      case (inr v₂) (fst (m₁⦃⇑ τ⦄)) (fst (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  fst (m₂⦃⇑ τ⦄)⦃v₂⦄ := .ιr
      _ =  fst (m₂⦃v₂ +: τ⦄) := by simp only [substCom]; rw [substUnion]
      _ ⇒⋆ fst (prod n₂ _)   := r₂'.fst
      _ ⇒  weakenJCom 0 n₂   := .π1
      _ ⇒⋆ n₂                := by rw [weakenJCom0]
    exact ℰ.bwdsRejoin r₁' r₂' hB₁

theorem sndCase {Γ δ} {Δ : Dtxt δ} {v m₁ m₂ B₁ B₂}
  (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊨ snd (case v m₁ m₂) ~ case v (snd m₁) (snd m₂) ∶ B₂ := by
  intro σ τ hστ φ ψ hφψ
  let ⟨_, n₁, _, n₂, r₁, r₂, hB₁⟩ := (soundCom hcase hστ .nil).snd
  have r₁' : snd ((case v m₁ m₂)⦃σ⦄) ⇒⋆ n₁ := by
    rw [← @weakenJCom0 n₁]; exact .trans' r₁.snd (.once .π2)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₁ (semCtxt.cons hA₁ hστ) .nil).snd
    have r' := Evals.merge (RTC.once .ιl) ⟨r₂, ⟨⟩⟩; rw [substUnion] at r'
    have r' := Evals.merge r' ⟨r₂', ⟨⟩⟩
    injection r'.prod_inv with _ en₁ en₂; subst en₁ en₂
    have r₂' :
      case (inl v₂) (snd (m₁⦃⇑ τ⦄)) (snd (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  snd (m₁⦃⇑ τ⦄)⦃v₂⦄ := .ιl
      _ =  snd (m₁⦃v₂ +: τ⦄) := by simp only [substCom]; rw [substUnion]
      _ ⇒⋆ snd (prod _ n₂)   := r₂'.snd
      _ ⇒  weakenJCom 0 n₂   := .π2
      _ ⇒⋆ n₂                := by rw [weakenJCom0]
    exact ℰ.bwdsRejoin r₁' r₂' hB₁
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₂ (semCtxt.cons hA₂ hστ) .nil).snd
    have r' := Evals.merge (RTC.once .ιr) ⟨r₂, ⟨⟩⟩; rw [substUnion] at r'
    have r' := Evals.merge r' ⟨r₂', ⟨⟩⟩
    injection r'.prod_inv with _ en₁ en₂; subst en₁ en₂
    have r₂' :
      case (inr v₂) (snd (m₁⦃⇑ τ⦄)) (snd (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  snd (m₂⦃⇑ τ⦄)⦃v₂⦄ := .ιr
      _ =  snd (m₂⦃v₂ +: τ⦄) := by simp only [substCom]; rw [substUnion]
      _ ⇒⋆ snd (prod _ n₂)   := r₂'.snd
      _ ⇒  weakenJCom 0 n₂   := .π2
      _ ⇒⋆ n₂                := by rw [weakenJCom0]
    exact ℰ.bwdsRejoin r₁' r₂' hB₁

theorem joinJoin {Γ δ} {Δ : Dtxt δ} {n₁ n₂ m A₁ A₂ B} (hn₁ : Γ ∷ A₁ ∣ Δ ⊢ n₁ ∶ B) (hn₂ : Γ ∷ A₂ ∣ Δ ∷ A₁ ↗ B ⊢ n₂ ∶ B) (hm : Γ ∣ Δ ∷ A₂ ↗ B ⊢ m ∶ B) :
  Γ ∣ Δ ⊨ join (join (renameCom (lift succ) n₁) n₂) m ~ join n₁ (join n₂ (renameJCom (liftJ .succ) m)) ∶ B := by
  intro σ τ hστ φ ψ hφψ
  have hright := soundCom (.join hn₁ (.join hn₂ (wtRenameJ (wRenameJLift wRenameJSucc) hm))) hστ hφψ
  unfold ℰ at hright
  let ⟨_, m₂, _, rm₂, _⟩ := hright
  have nfm₂ := rm₂.2
  simp [renameJSubst] at rm₂; simp [renameJSubst]
  match rm₂.wkJoin₂ with
  | .inl ⟨v, rm, rjoin, rm₂⟩ =>
    have hleft := soundCom (.join (.join (wtRenameCom (wRenameLift wRenameSucc) hn₁) hn₂) hm) hστ hφψ
    unfold ℰ at hleft
    let ⟨_, _, rm₁, rm₂', hB⟩ := hleft
    let r : _ ⇒⋆ m₂ := by
      calc rejoin (join ((join (renameCom (lift succ) n₁) n₂)⦃⇑ τ⦄) (m⦃τ⦄)) ψ
      _ ⇒⋆ rejoin (join ((join (renameCom (lift succ) n₁) n₂)⦃⇑ τ⦄) (jump 0 v)) ψ := .rejoin (.join rm)
      _ ⇒ rejoin ((join (renameCom (lift succ) n₁) n₂)⦃⇑ τ⦄⦃v⦄) ψ := .rejoin .γ
      _ = rejoin (join (n₁⦃⇑ τ⦄) (n₂⦃v +: τ⦄)) ψ := by rw [substUnion]; simp; rw [renameUpSubstConsCom]
      _ ⇒⋆ m₂ := by rw [substUnion] at rm₂; exact rm₂
    have rn := r.merge rm₂'
    unfold ℰ; exact ⟨_, _, rm₁, ⟨.trans' rjoin (.trans' rm₂ rn), rm₂'.2⟩, hB⟩
  | .inr ⟨m', rm, rjoin, rm₂⟩ =>
    have hleft := soundCom (.join (.join (wtRenameCom (wRenameLift wRenameSucc) hn₁) hn₂) hm) hστ hφψ
    unfold ℰ at hleft
    let ⟨_, _, rm₁, rm₂', hB⟩ := hleft
    have rn := Evals.merge (.rejoin (.join rm)) rm₂'
    let ⟨_, rm', _, rn⟩ := Norm.wkJoin ⟨rn, rm₂'.2⟩
    have rn := Evals.merge rm₂ ⟨.trans' (Evals.rejoin rm') rn, rm₂'.2⟩
    unfold ℰ; exact ⟨_, _, rm₁, ⟨.trans' rjoin (.trans' rm₂ rn), rm₂'.2⟩, hB⟩

theorem dropJoin {Γ δ} {Δ : Dtxt δ} {m₁ m₂ A B} (h₁ : Γ ∷ A ∣ Δ ⊢ m₁ ∶ B) (h₂ : Γ ∣ Δ ⊢ m₂ ∶ B) :
  Γ ∣ Δ ⊨ m₂ ~ (join m₁ (renameJCom Fin.succ m₂)) ∶ B := by
  intro σ τ hστ φ ψ hφψ
  -- get rid of join m₁
  have hm₂ := soundCom (.join h₁ (wtWeakenJ h₂)) hστ hφψ
  unfold ℰ at hm₂
  let ⟨_, n₂, _, rn₂, _⟩ := hm₂
  have nfn₂ := rn₂.2
  simp [renameJSubst] at rn₂; simp [renameJSubst]
  let ⟨_, rm₂, rjoin, rn₂⟩ := rn₂.wkJoin
  refine ℰ.bwds .refl (.trans' rjoin rn₂) ?_
  -- merge reductions
  have hm₂ := soundCom h₂ hστ hφψ
  unfold ℰ at hm₂
  let ⟨_, n₂', rn₁, rn₂', hB⟩ := hm₂
  have rn := Evals.merge (RTC.trans' rm₂.rejoin rn₂) rn₂'
  unfold ℰ; exact ⟨_, _, rn₁, ⟨rn, rn₂'.2⟩, hB⟩

theorem caseCase {Γ δ} {Δ : Dtxt δ} {v m₁ m₂ m₃ m₄ B} {A₁ A₂ A₃ A₄ : ValType}
  (hv : Γ ⊢ v ∶ Sum A₃ A₄)
  (hm₁ : Γ ∷ A₁ ∣ Δ ⊢ m₁ ∶ B)
  (hm₂ : Γ ∷ A₂ ∣ Δ ⊢ m₂ ∶ B)
  (hm₃ : Γ ∷ A₃ ∣ ⬝ ⊢ m₃ ∶ F (Sum A₁ A₂))
  (hm₄ : Γ ∷ A₄ ∣ ⬝ ⊢ m₄ ∶ F (Sum A₁ A₂)) :
  Γ ∣ Δ ⊨ join (case (var 0) (renameCom (lift succ) m₁) (renameCom (lift succ) m₂))
            (case v (letin m₃ (jump 0 (var 0))) (letin m₄ (jump 0 (var 0))))
        ~ join m₁ (join (renameJCom Fin.succ m₂)
            (case v (letin m₃ (case (var 0) (jump 1 (var 0)) (jump 0 (var 0))))
                    (letin m₄ (case (var 0) (jump 1 (var 0)) (jump 0 (var 0)))))) ∶ B := by
  intro σ τ hστ φ ψ hφψ
  have hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₃, e₁, e₂⟩ =>
    simp only [substCom]; rw [e₁, e₂]
    refine ℰ.bwd (.rejoin (.join .ιl)) (.rejoin (.join (.join .ιl))) ?_
    simp only [substCom]; rw [substUnion, substUnion]
    have ⟨w₁, w₂, r₁, r₂, hA₁₂⟩ := (soundCom hm₃ (semCtxt.cons hA₃ hστ) .nil).ret_inv
    refine ℰ.bwds
      (.rejoin (.join (.trans' (Evals.letin r₁) (.once .ζ))))
      (.rejoin (.join (.join (.trans' (Evals.letin r₂) (.once .ζ))))) ?_
    unfold 𝒱 at hA₁₂
    match hA₁₂ with
    | .inl ⟨w₁', w₂', hA₁, e₁, e₂⟩ =>
      subst e₁ e₂
      refine ℰ.bwds
        (.rejoin (.trans .γ (.once .ιl)))
        (.rejoin (.trans' (Evals.join (.trans (.join .ιl) (.once (.join't (j := 0))))) (.once .γ))) ?_
      rw [substUnion, substUnion, substUnion₂, substDrop₂]; simp [up]
      exact soundCom hm₁ (semCtxt.cons hA₁ hστ) hφψ
    | .inr ⟨w₁', w₂', hA₂, e₁, e₂⟩ =>
      subst e₁ e₂
      refine ℰ.bwds
        (.rejoin (.trans .γ (.once .ιr)))
        (.rejoin (.join (.trans (.join .ιr) (.once .γ)))) ?_
      rw [substUnion, substUnion, substUnion₂, substDrop₂]; simp [up]
      have hB := dropJoin (wtWeakenCom₂ hm₁) hm₂ (semCtxt.cons hA₂ hστ) hφψ
      simp [renameUpSubstConsCom] at hB; exact hB
  | .inr ⟨v₁, v₂, hA₄, e₁, e₂⟩ =>
    simp only [substCom]; rw [e₁, e₂]
    refine ℰ.bwd (.rejoin (.join .ιr)) (.rejoin (.join (.join .ιr))) ?_
    simp only [substCom]; rw [substUnion, substUnion]
    have ⟨w₁, w₂, r₁, r₂, hA₁₂⟩ := (soundCom hm₄ (semCtxt.cons hA₄ hστ) .nil).ret_inv
    refine ℰ.bwds
      (.rejoin (.join (.trans' (Evals.letin r₁) (.once .ζ))))
      (.rejoin (.join (.join (.trans' (Evals.letin r₂) (.once .ζ))))) ?_
    unfold 𝒱 at hA₁₂
    match hA₁₂ with
    | .inl ⟨w₁', w₂', hA₁, e₁, e₂⟩ =>
      subst e₁ e₂
      refine ℰ.bwds
        (.rejoin (.trans .γ (.once .ιl)))
        (.rejoin (.trans' (Evals.join (.trans (.join .ιl) (.once (.join't (j := 0))))) (.once .γ))) ?_
      rw [substUnion, substUnion, substUnion₂, substDrop₂]; simp [up]
      exact soundCom hm₁ (semCtxt.cons hA₁ hστ) hφψ
    | .inr ⟨w₁', w₂', hA₂, e₁, e₂⟩ =>
      subst e₁ e₂
      refine ℰ.bwds
        (.rejoin (.trans .γ (.once .ιr)))
        (.rejoin (.join (.trans (.join .ιr) (.once .γ)))) ?_
      rw [substUnion, substUnion, substUnion₂, substDrop₂]; simp [up]
      have hB := dropJoin (wtWeakenCom₂ hm₁) hm₂ (semCtxt.cons hA₂ hστ) hφψ
      simp [renameUpSubstConsCom] at hB; exact hB
