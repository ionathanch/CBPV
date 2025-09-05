import CBPV.Equivalence

open Nat ValType ComType Val Com

theorem letLet {Γ Δ n m m' A} {B : ComType}
  (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ F A)
  (hm' : Γ ∷ A ∣ Δ ⊢ m' ∶ B) :
  Γ ∣ Δ ⊨ letin (letin n m) m' ~ letin n (letin m (renameCom (lift succ) m')) ∶ B := by
  intro σ τ hστ js₁ js₂ hjs
  let ⟨v₁, v₂, rv₁, rv₂, hA⟩ := (soundCom hlet hστ .nil).ret_inv
  have r₁' : letin ((letin n m)⦃σ⦄) (m'⦃⇑ σ⦄) ⇒⋆ m'⦃v₁ +: σ⦄ := by
    rw [← substUnion]; exact .trans' rv₁.letin (.once .ζ)
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, rw₁, rw₂, _⟩ := (soundCom hn hστ .nil).ret_inv
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ m⦃w₂ +: τ⦄ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.letin
    _ ⇒  m⦃w₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
  let ⟨_, rlet₁, rlet₂⟩ := confluence rv₂ rlet
  rw [← rlet₁.ret_inv] at rlet₂
  have r₂' : (letin n (letin m (renameCom (lift succ) m')))⦃τ⦄ ⇒⋆ m'⦃v₂ +: τ⦄ := calc
    _ ⇒⋆ letin (ret w₂) (letin (m⦃⇑ τ⦄) ((renameCom (lift succ) m')⦃⇑⇑ τ⦄))
      := by simp only [substCom]; exact rw₂.letin
    _ ⇒ (letin (m⦃⇑ τ⦄) ((renameCom (lift succ) m')⦃⇑⇑ τ⦄))⦃w₂⦄ := .ζ
    _ = letin (m⦃w₂ +: τ⦄) (m'⦃⇑τ⦄)
      := by simp only [substCom]; rw [substUnion, renameDropSubst]
    _ ⇒⋆ letin (ret v₂) (m'⦃⇑τ⦄) := rlet₂.letin
    _ ⇒ m'⦃v₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
  have goal := soundCom hm' (semCtxt.cons hA hστ) hjs
  refine ℰ.bwds (.rejoin r₁') (.rejoin r₂') goal

theorem appLet {Γ Δ n m v A B}
  (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Arr A B)
  (hv : Γ ⊢ v ∶ A) :
  Γ ∣ Δ ⊨ app (letin n m) v ~ letin n (app m (renameVal succ v)) ∶ B := by
  intro σ τ hστ js₁ js₂ hjs
  let ⟨n₁, n₂, r₁, r₂, hB⟩ := (soundCom hlet hστ .nil).lam_inv
  have r₁' : app ((letin n m)⦃σ⦄) (v⦃σ⦄) ⇒⋆ n₁⦃v⦃σ⦄⦄ := .trans' r₁.app (.once .β)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn hστ .nil).ret_inv
  let ⟨_, m₂, _, rm₂, _⟩ := (soundCom hm (semCtxt.cons hA' hστ) .nil).lam_inv
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ lam m₂ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.letin
    _ ⇒  m⦃w₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
    _ ⇒⋆ lam m₂ := rm₂
  let ⟨_, rlam₁, rlam₂⟩ := confluence r₂ rlet
  rw [← rlam₂.lam_inv] at rlam₁; injection rlam₁.lam_inv with e; subst e
  clear rlet rlam₁ rlam₂
  have r₂' : letin (n⦃τ⦄) (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄))
      ⇒⋆ n₂⦃v⦃τ⦄⦄ := calc
    _ ⇒⋆ letin (ret w₂) (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄)) := rw₂.letin
    _ ⇒  (app (m⦃⇑ τ⦄) (renameVal succ v⦃⇑ τ⦄))⦃w₂⦄ := .ζ
    _ = app (m⦃w₂ +: τ⦄) (v⦃τ⦄)
      := by simp only [substCom]; rw [substUnion, renameUpSubstVal, substDropVal]
    _ ⇒⋆ app (lam n₂) (v⦃τ⦄) := rm₂.app
    _ ⇒  n₂⦃v⦃τ⦄⦄ := .β
  exact ℰ.bwdsRejoin r₁' r₂' (hB _ _ (soundVal hv hστ))

theorem fstLet {Γ Δ n m B₁ B₂}
  (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊨ fst (letin n m) ~ letin n (fst m) ∶ B₁ := by
  intro σ τ hστ js₁ js₂ hjs
  let ⟨n₁, _, n₂, _, r₁, r₂, hB₁⟩ := (soundCom hlet hστ .nil).fst
  have r₁' : fst ((letin n m)⦃σ⦄) ⇒⋆ n₁ := .trans' r₁.fst (.once .π1)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn hστ .nil).ret_inv
  let ⟨m₁, _, m₂, _, _, r₂', _⟩ := (soundCom hm (semCtxt.cons hA' hστ) .nil).fst
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ prod m₂ _ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.letin
    _ ⇒  m⦃w₂ +: τ⦄              := by rw [← substUnion]; exact .ζ
    _ ⇒⋆ prod m₂ _               := r₂'
  let ⟨_, rprod₁, rprod₂⟩ := confluence r₂ rlet
  rw [← rprod₂.prod_inv] at rprod₁; injection rprod₁.prod_inv with e₁ e₂; subst e₁ e₂
  clear rlet rprod₁ rprod₂
  have r₂' : letin (n⦃τ⦄) (fst (m⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
    _ ⇒⋆ letin (ret w₂) (fst (m⦃⇑ τ⦄)) := rw₂.letin
    _ ⇒  fst (m⦃⇑ τ⦄⦃w₂⦄)              := .ζ
    _ =  fst (m⦃w₂ +: τ⦄)              := by rw [substUnion]
    _ ⇒⋆ fst (prod n₂ _)               := r₂'.fst
    _ ⇒  n₂                            := .π1
  exact ℰ.bwdsRejoin r₁' r₂' hB₁

theorem sndLet {Γ Δ n m B₁ B₂}
  (hlet : Γ ∣ ⬝ ⊢ letin n m ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊨ snd (letin n m) ~ letin n (snd m) ∶ B₂ := by
  intro σ τ hστ js₁ js₂ hjs
  let ⟨_, n₁, _, n₂, r₁, r₂, hB₂⟩ := (soundCom hlet hστ .nil).snd
  have r₁' : snd ((letin n m)⦃σ⦄) ⇒⋆ n₁ := .trans' r₁.snd (.once .π2)
  simp only [substCom] at *
  cases hlet with | letin hn hm =>
  let ⟨w₁, w₂, _, rw₂, hA'⟩ := (soundCom hn hστ .nil).ret_inv
  let ⟨m₁, _, m₂, _, _, r₂', _⟩ := (soundCom hm (semCtxt.cons hA' hστ) .nil).fst
  have rlet : letin (n⦃τ⦄) (m⦃⇑ τ⦄) ⇒⋆ prod m₂ _ := calc
    _ ⇒⋆ letin (ret w₂) (m⦃⇑ τ⦄) := rw₂.letin
    _ ⇒  m⦃w₂ +: τ⦄              := by rw [← substUnion]; exact .ζ
    _ ⇒⋆ prod m₂ _               := r₂'
  let ⟨_, rprod₁, rprod₂⟩ := confluence r₂ rlet
  rw [← rprod₂.prod_inv] at rprod₁; injection rprod₁.prod_inv with e₁ e₂; subst e₁ e₂
  clear rlet rprod₁ rprod₂
  have r₂' : letin (n⦃τ⦄) (snd (m⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
    _ ⇒⋆ letin (ret w₂) (snd (m⦃⇑ τ⦄)) := rw₂.letin
    _ ⇒  snd (m⦃⇑ τ⦄⦃w₂⦄)              := .ζ
    _ =  snd (m⦃w₂ +: τ⦄)              := by rw [substUnion]
    _ ⇒⋆ snd (prod _ n₂)               := r₂'.snd
    _ ⇒  n₂                            := .π2
  exact ℰ.bwdsRejoin r₁' r₂' hB₂

theorem letCase {Γ Δ v m₁ m₂ n A} {B : ComType}
  (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ F A)
  (hn : Γ ∷ A ∣ Δ ⊢ n ∶ B) :
  Γ ∣ Δ ⊨ letin (case v m₁ m₂) n
    ~ case v (letin m₁ (renameCom (lift succ) n)) (letin m₂ (renameCom (lift succ) n)) ∶ B := by
  intro σ τ hστ js₁ js₂ hjs
  let ⟨v₁, v₂, rv₁, rv₂, hA⟩ := (soundCom hcase hστ .nil).ret_inv
  have r₁' : letin ((case v m₁ m₂)⦃σ⦄) (n⦃⇑ σ⦄) ⇒⋆ n⦃v₁ +: σ⦄ := by
    rw [← substUnion]; exact .trans' rv₁.letin (.once .ζ)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨w₁, w₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at rv₂
    let ⟨n₁, n₂, rn₁, rn₂, _⟩ := (soundCom hm₁ (semCtxt.cons hA₁ hστ) .nil).ret_inv
    let rcase : case (inl w₂) (m₁⦃⇑ τ⦄) (m₂⦃⇑ τ⦄) ⇒⋆ ret n₂ := calc
      _ ⇒ m₁⦃w₂ +: τ⦄ := by rw [← substUnion]; exact .ιl
      _ ⇒⋆ ret n₂     := rn₂
    let ⟨_, rret₁, rret₂⟩ := confluence rv₂ rcase
    rw [← rret₂.ret_inv] at rret₁; injection rret₁.ret_inv with e; subst e
    clear rcase rret₁ rret₂
    have r₂' : case (inl w₂)
                    (letin (m₁⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))
                    (letin (m₂⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))
               ⇒⋆ n⦃v₂ +: τ⦄ := calc
        _ ⇒ (letin (m₁⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))⦃w₂⦄ := .ιl
        _ ⇒⋆ letin (m₁⦃w₂ +: τ⦄) (n⦃⇑τ⦄)
          := by simp only [substCom]; rw [substUnion, renameDropSubst]
        _ ⇒⋆ letin (ret v₂) (n⦃⇑ τ⦄) := rn₂.letin
        _ ⇒ n⦃v₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
    have goal := soundCom hn (semCtxt.cons hA hστ) hjs
    exact ℰ.bwds (.rejoin r₁') (.rejoin r₂') goal
  | .inr ⟨w₁, w₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at rv₂
    let ⟨n₁, n₂, rn₁, rn₂, _⟩ := (soundCom hm₂ (semCtxt.cons hA₂ hστ) .nil).ret_inv
    let rcase : case (inr w₂) (m₁⦃⇑ τ⦄) (m₂⦃⇑ τ⦄) ⇒⋆ ret n₂ := calc
      _ ⇒ m₂⦃w₂ +: τ⦄ := by rw [← substUnion]; exact .ιr
      _ ⇒⋆ ret n₂     := rn₂
    let ⟨_, rret₁, rret₂⟩ := confluence rv₂ rcase
    rw [← rret₂.ret_inv] at rret₁; injection rret₁.ret_inv with e; subst e
    clear rcase rret₁ rret₂
    have r₂' : case (inr w₂)
                    (letin (m₁⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))
                    (letin (m₂⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))
               ⇒⋆ n⦃v₂ +: τ⦄ := calc
        _ ⇒ (letin (m₂⦃⇑τ⦄) (renameCom (lift succ) n⦃⇑⇑τ⦄))⦃w₂⦄ := .ιr
        _ ⇒⋆ letin (m₂⦃w₂ +: τ⦄) (n⦃⇑τ⦄)
          := by simp only [substCom]; rw [substUnion, renameDropSubst]
        _ ⇒⋆ letin (ret v₂) (n⦃⇑ τ⦄) := rn₂.letin
        _ ⇒ n⦃v₂ +: τ⦄ := by rw [← substUnion]; exact .ζ
    have goal := soundCom hn (semCtxt.cons hA hστ) hjs
    exact ℰ.bwds (.rejoin r₁') (.rejoin r₂') goal

theorem appCase {Γ Δ v w m₁ m₂ A B}
  (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Arr A B)
  (hw : Γ ⊢ w ∶ A) :
  Γ ∣ Δ ⊨ app (case v m₁ m₂) w ~ case v (app m₁ (renameVal succ w)) (app m₂ (renameVal succ w)) ∶ B := by
  intro σ τ hστ js₁ js₂ hjs
  let ⟨n₁, n₂, r₁, r₂, hB₁⟩ := (soundCom hcase hστ .nil).lam_inv
  have r₁' : app ((case v m₁ m₂)⦃σ⦄) (w⦃σ⦄) ⇒⋆ n₁⦃w⦃σ⦄⦄ := .trans' r₁.app (.once .β)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, r₂', _⟩ := (soundCom hm₁ (semCtxt.cons hA₁ hστ) .nil).lam_inv
    let ⟨_, rlam₁, r'⟩ := confluence r₂ (.once .ιl); rw [substUnion] at r'
    let ⟨_, rlam₂, r'⟩ := confluence r₂' r'; rw [← rlam₂.lam_inv] at r'
    injection Evals.lam_inv (.trans' rlam₁ r') with en₂; subst en₂
    clear rlam₁ rlam₂ r' r₁; clear r'
    have r₂' :
      case (.inl v₂) (app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄)) (app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄))
        ⇒⋆ n₂⦃w⦃τ⦄⦄ := calc
      _ ⇒  app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄) ⦃v₂⦄ := .ιl
      _ =  app (m₁⦃v₂ +: τ⦄) (w⦃τ⦄)
        := by simp only [substCom]; rw [substUnion, renameUpSubstVal, substDropVal]
      _ ⇒⋆ app (lam n₂) (w⦃τ⦄) := r₂'.app
      _ ⇒  n₂⦃w⦃τ⦄⦄ := .β
    exact ℰ.bwdsRejoin r₁' r₂' (hB₁ _ _ (soundVal hw hστ))
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, r₂', _⟩ := (soundCom hm₂ (semCtxt.cons hA₂ hστ) .nil).lam_inv
    let ⟨_, rlam₁, r'⟩ := confluence r₂ (.once .ιr); rw [substUnion] at r'
    let ⟨_, rlam₂, r'⟩ := confluence r₂' r'; rw [← rlam₂.lam_inv] at r'
    injection Evals.lam_inv (.trans' rlam₁ r') with en₂; subst en₂
    clear rlam₁ rlam₂ r' r₁; clear r'
    have r₂' :
      case (.inr v₂) (app (m₁⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄)) (app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄))
        ⇒⋆ n₂⦃w⦃τ⦄⦄ := calc
      _ ⇒  app (m₂⦃⇑ τ⦄) (renameVal succ w⦃⇑ τ⦄) ⦃v₂⦄ := .ιr
      _ =  app (m₂⦃v₂ +: τ⦄) (w⦃τ⦄)
        := by simp only [substCom]; rw [substUnion, renameUpSubstVal, substDropVal]
      _ ⇒⋆ app (lam n₂) (w⦃τ⦄) := r₂'.app
      _ ⇒  n₂⦃w⦃τ⦄⦄ := .β
    exact ℰ.bwdsRejoin r₁' r₂' (hB₁ _ _ (soundVal hw hστ))

theorem fstCase {Γ Δ v m₁ m₂ B₁ B₂}
  (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊨ fst (case v m₁ m₂) ~ case v (fst m₁) (fst m₂) ∶ B₁ := by
  intro σ τ hστ js₁ js₂ hjs
  let ⟨n₁, _, n₂, _, r₁, r₂, hB₁⟩ := (soundCom hcase hστ .nil).fst
  have r₁' : fst ((case v m₁ m₂)⦃σ⦄) ⇒⋆ n₁ := .trans' r₁.fst (.once .π1)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₁ (semCtxt.cons hA₁ hστ) .nil).fst
    let ⟨_, rprod₁, r'⟩ := confluence r₂ (.once .ιl); rw [substUnion] at r'
    let ⟨_, rprod₂, r'⟩ := confluence r₂' r'; rw [← rprod₂.prod_inv] at r'
    injection Evals.prod_inv (.trans' rprod₁ r') with en₁ en₂; subst en₁ en₂
    clear rprod₁ rprod₂ r' r₁; clear r'
    have r₂' :
      case (inl v₂) (fst (m₁⦃⇑ τ⦄)) (fst (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  fst (m₁⦃⇑ τ⦄)⦃v₂⦄ := .ιl
      _ =  fst (m₁⦃v₂ +: τ⦄) := by simp only [substCom]; rw [substUnion]
      _ ⇒⋆ fst (prod n₂ _)   := r₂'.fst
      _ ⇒ n₂                 := .π1
    exact ℰ.bwdsRejoin r₁' r₂' hB₁
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₂ (semCtxt.cons hA₂ hστ) .nil).fst
    let ⟨_, rprod₁, r'⟩ := confluence r₂ (.once .ιr); rw [substUnion] at r'
    let ⟨_, rprod₂, r'⟩ := confluence r₂' r'; rw [← rprod₂.prod_inv] at r'
    injection Evals.prod_inv (.trans' rprod₁ r') with en₁ en₂; subst en₁ en₂
    clear rprod₁ rprod₂ r' r₁; clear r'
    have r₂' :
      case (inr v₂) (fst (m₁⦃⇑ τ⦄)) (fst (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  fst (m₂⦃⇑ τ⦄)⦃v₂⦄ := .ιr
      _ =  fst (m₂⦃v₂ +: τ⦄) := by simp only [substCom]; rw [substUnion]
      _ ⇒⋆ fst (prod n₂ _)   := r₂'.fst
      _ ⇒ n₂                 := .π1
    exact ℰ.bwdsRejoin r₁' r₂' hB₁

theorem sndCase {Γ Δ v m₁ m₂ B₁ B₂}
  (hcase : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ Prod B₁ B₂) :
  Γ ∣ Δ ⊨ snd (case v m₁ m₂) ~ case v (snd m₁) (snd m₂) ∶ B₂ := by
  intro σ τ hστ js₁ js₂ hjs
  let ⟨_, n₁, _, n₂, r₁, r₂, hB₁⟩ := (soundCom hcase hστ .nil).snd
  have r₁' : snd ((case v m₁ m₂)⦃σ⦄) ⇒⋆ n₁ := .trans' r₁.snd (.once .π2)
  simp only [substCom] at *
  cases hcase with | case hv hm₁ hm₂ =>
  let hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₁, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₁ (semCtxt.cons hA₁ hστ) .nil).snd
    let ⟨_, rprod₁, r'⟩ := confluence r₂ (.once .ιl); rw [substUnion] at r'
    let ⟨_, rprod₂, r'⟩ := confluence r₂' r'; rw [← rprod₂.prod_inv] at r'
    injection Evals.prod_inv (.trans' rprod₁ r') with en₁ en₂; subst en₁ en₂
    clear rprod₁ rprod₂ r' r₁; clear r'
    have r₂' :
      case (inl v₂) (snd (m₁⦃⇑ τ⦄)) (snd (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  snd (m₁⦃⇑ τ⦄)⦃v₂⦄ := .ιl
      _ =  snd (m₁⦃v₂ +: τ⦄) := by simp only [substCom]; rw [substUnion]
      _ ⇒⋆ snd (prod _ n₂)   := r₂'.snd
      _ ⇒ n₂                 := .π2
    exact ℰ.bwdsRejoin r₁' r₂' hB₁
  | .inr ⟨v₁, v₂, hA₂, e₁, e₂⟩ =>
    rw [e₂]; rw [e₂] at r₂
    let ⟨_, _, _, _, _, r₂', _⟩ := (soundCom hm₂ (semCtxt.cons hA₂ hστ) .nil).snd
    let ⟨_, rprod₁, r'⟩ := confluence r₂ (.once .ιr); rw [substUnion] at r'
    let ⟨_, rprod₂, r'⟩ := confluence r₂' r'; rw [← rprod₂.prod_inv] at r'
    injection Evals.prod_inv (.trans' rprod₁ r') with en₁ en₂; subst en₁ en₂
    clear rprod₁ rprod₂ r' r₁; clear r'
    have r₂' :
      case (inr v₂) (snd (m₁⦃⇑ τ⦄)) (snd (m₂⦃⇑ τ⦄)) ⇒⋆ n₂ := calc
      _ ⇒  snd (m₂⦃⇑ τ⦄)⦃v₂⦄ := .ιr
      _ =  snd (m₂⦃v₂ +: τ⦄) := by simp only [substCom]; rw [substUnion]
      _ ⇒⋆ snd (prod _ n₂)   := r₂'.snd
      _ ⇒ n₂                 := .π2
    exact ℰ.bwdsRejoin r₁' r₂' hB₁

theorem caseOfCase {Γ Δ v m₁ m₂ m₃ m₄ B} {A₁ A₂ A₃ A₄ : ValType}
  (hv : Γ ⊢ v ∶ Sum A₃ A₄)
  (hm₁ : Γ ∷ A₁ ∣ Δ ⊢ m₁ ∶ B)
  (hm₂ : Γ ∷ A₂ ∣ Δ ⊢ m₂ ∶ B)
  (hm₃ : Γ ∷ A₃ ∣ ⬝ ⊢ m₃ ∶ F (Sum A₁ A₂))
  (hm₄ : Γ ∷ A₄ ∣ ⬝ ⊢ m₄ ∶ F (Sum A₁ A₂)) :
  Γ ∣ Δ ⊨ join (case (var 0) m₁ m₂) (case v (letin m₃ (jump 0 (var 0))) (letin m₄ (jump 0 (var 0))))
        ~ join m₁ (join (renameJCom succ m₂)
            (case v (letin m₃ (case (var 0) (jump 1 (var 0)) (jump 0 (var 0))))
                    (letin m₄ (case (var 0) (jump 1 (var 0)) (jump 0 (var 0)))))) ∶ B := by
  intro σ τ hστ js₁ js₂ hjs
  have hv := soundVal hv hστ; unfold 𝒱 at hv
  match hv with
  | .inl ⟨v₁, v₂, hA₃, e₁, e₂⟩ =>
    simp only [substCom]; rw [e₁, e₂]
    refine ℰ.bwd (.rejoin (.join .ιl)) (.rejoin (.join (.join .ιl))) ?_
    have ⟨w₁, w₂, r₁, r₂, hA₁₂⟩ := (soundCom hm₃ (semCtxt.cons hA₃ hστ) .nil).ret_inv
    simp only [substCom]; rw [substUnion, substUnion]
    refine ℰ.bwds
      (.rejoin (.join (.trans' (Evals.letin r₁) (.once .ζ))))
      (.rejoin (.join (.join (.trans' (Evals.letin r₂) (.once .ζ))))) ?_
    have e₂ σ v : ((var 0)⦃⇑⇑ σ⦄⦃⇑ (v +: var)⦄) = var 0 := by simp [lift, up]
    have e₃ τ v : ((var 0)⦃⇑⇑⇑ τ⦄⦃⇑⇑ (v +: var)⦄) = var 0 := by simp [lift, up]
    have e σ : (⇑ σ) 0 = var 0 := rfl
    rw [e₂ σ v₁, e₂ τ v₂, e₃ τ v₂]; simp [substCom]; rw [e σ, e (w₂ +: var)]
    unfold 𝒱 at hA₁₂
    match hA₁₂ with
    | .inl ⟨w₁', w₂', hA₁, e₁, e₂⟩ =>
      subst e₁ e₂
      refine ℰ.bwd (.rejoin .γ) (.rejoin (.join (.join .ιl))) ?_; simp
      refine ℰ.bwds (.rejoin (.once .ιl)) (.rejoin (.trans (.join .join't) (.once .γ))) ?_
      rw [substUnion, substUnion, substUnion₂]
      have hB := soundCom hm₁ (semCtxt.cons hA₁ hστ) hjs
      sorry
    | .inr ⟨w₁', w₂', hA₂, e₁, e₂⟩ =>
      subst e₁ e₂
      refine ℰ.bwd (.rejoin .γ) (.rejoin (.join (.join .ιr))) ?_; simp
      refine ℰ.bwds (.rejoin (.once .ιr)) (.rejoin (.join (.once .γ))) ?_
      rw [substUnion, substUnion, substUnion₂]
      have hB := soundCom hm₂ (semCtxt.cons hA₂ hστ) hjs
      sorry
  | .inr ⟨_, _, _, e₁, e₂⟩ => sorry
