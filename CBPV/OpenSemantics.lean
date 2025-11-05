import CBPV.NormalInd

open ValType ComType Val Com

/-*--------------------------
  Logical relation on types
--------------------------*-/

section
set_option hygiene false
local notation:40 "⟦" A:41 "⟧ᵛ" "↘" P:41 => 𝒱 A P
local notation:40 "⟦" B:41 "⟧ᶜ" "↘" P:41 => 𝒞 B P

mutual
inductive 𝒱 : ValType → (Val → Prop) → Prop where
  | Unit : ⟦ Unit ⟧ᵛ ↘ (λ v ↦ SNeVal v ∨ v = unit)
  | Sum {A₁ A₂ P Q} :
    ⟦ A₁ ⟧ᵛ ↘ P →
    ⟦ A₂ ⟧ᵛ ↘ Q →
    ----------------------------------
    ⟦ Sum A₁ A₂ ⟧ᵛ ↘ (λ v ↦ SNeVal v ∨
      (∃ w, v = inl w ∧ P w) ∨
      (∃ w, v = inr w ∧ Q w))
  | Pair {A₁ A₂ P Q} :
    ⟦ A₁ ⟧ᵛ ↘ P →
    ⟦ A₂ ⟧ᵛ ↘ Q →
    ----------------------------------------
    ⟦ Pair A₁ A₂ ⟧ᵛ ↘ (λ v ↦ SNeVal v ∨
      ∃ w₁ w₂, v = pair w₁ w₂ ∧ P w₁ ∧ Q w₂)
  | U {B P} :
    ⟦ B ⟧ᶜ ↘ P →
    ------------------------------
    ⟦ U B ⟧ᵛ ↘ (λ v ↦ P (force v))

inductive 𝒞 : ComType → (Com → Prop) → Prop where
  | F {A P} :
    ⟦ A ⟧ᵛ ↘ P →
    ----------------------------------------------------------------------
    ⟦ F A ⟧ᶜ ↘ (λ m ↦ (∃ n, m ⤳⋆ n ∧ SNeCom n) ∨ (∃ v, m ⤳⋆ ret v ∧ P v))
  | Arr {A B P Q} :
    ⟦ A ⟧ᵛ ↘ P →
    ⟦ B ⟧ᶜ ↘ Q →
    ---------------------------------------------
    ⟦ Arr A B ⟧ᶜ ↘ (λ m ↦ ∀ v, P v → Q (app m v))
  | Prod {B₁ B₂ P Q} :
    ⟦ B₁ ⟧ᶜ ↘ P →
    ⟦ B₂ ⟧ᶜ ↘ Q →
    ----------------------------------------------------------------------------------------------
    ⟦ Prod B₁ B₂ ⟧ᶜ ↘ (λ m ↦ (∃ n, m ⤳⋆ n ∧ SNeCom n) ∨ (∃ n₁ n₂, m ⤳⋆ prod n₁ n₂ ∧ P n₁ ∧ Q n₂))
end
end

notation:40 "⟦" A:41 "⟧ᵛ" "↘" P:41 => 𝒱 A P
notation:40 "⟦" B:41 "⟧ᶜ" "↘" P:41 => 𝒞 B P

joint
  theorem ValType.interp A : ∃ P, ⟦ A ⟧ᵛ ↘ P
  theorem ComType.interp B : ∃ P, ⟦ B ⟧ᶜ ↘ P
by
  mutual_induction A, B
  case Unit => exact ⟨_, .Unit⟩
  case Sum ihA ihB =>
    let ⟨_, hA⟩ := ihA
    let ⟨_, hB⟩ := ihB
    exact ⟨_, .Sum hA hB⟩
  case Pair ihA ihB =>
    let ⟨_, hA⟩ := ihA
    let ⟨_, hB⟩ := ihB
    exact ⟨_, .Pair hA hB⟩
  case U ih => let ⟨_, h⟩ := ih; exact ⟨_, .U h⟩
  case F ih => let ⟨_, h⟩ := ih; exact ⟨_, .F h⟩
  case Arr ihA ihB =>
    let ⟨_, hA⟩ := ihA
    let ⟨_, hB⟩ := ihB
    exact ⟨_, .Arr hA hB⟩
  case Prod ihA ihB =>
    let ⟨_, hA⟩ := ihA
    let ⟨_, hB⟩ := ihB
    exact ⟨_, .Prod hA hB⟩

/-*-----------------------------------------------------
  Properties of the logical relation:
  * Interpretation of a type is deterministic
  * Backward closure wrt strong reduction
  * Interpretations contain all strongly neutral terms
  * Terms in interpretations are strongly normalizing
-----------------------------------------------------*-/

joint
  theorem 𝒱.det {A P Q} (h : ⟦ A ⟧ᵛ ↘ P) : ⟦ A ⟧ᵛ ↘ Q → P = Q
  theorem 𝒞.det {B P Q} (h : ⟦ B ⟧ᶜ ↘ P) : ⟦ B ⟧ᶜ ↘ Q → P = Q
by
  mutual_induction h, h
  case Unit => intro h; cases h; rfl
  case Sum ihA ihB =>
    intro h; cases h with | Sum hA hB => rw [ihA hA, ihB hB]
  case Pair ihA ihB =>
    intro h; cases h with | Pair hA hB => rw [ihA hA, ihB hB]
  case U ih =>
    intro h; cases h with | U hB => rw [ih hB]
  case F ih =>
    intro h; cases h with | F hA => rw [ih hA]
  case Arr ihA ihB =>
    intro h; cases h with | Arr hA hB => rw [ihA hA, ihB hB]
  case Prod ihA ihB =>
    intro h; cases h with | Prod hA hB => rw [ihA hA, ihB hB]

theorem 𝒞.closure {B P} {m n : Com} (h : ⟦ B ⟧ᶜ ↘ P) (r : m ⤳⋆ n) : P n → P m := by
  mutual_induction h generalizing m n <;> intro p
  case F =>
    match p with
    | .inl ⟨_, r', sne⟩ => exact .inl ⟨_, .trans' r r', sne⟩
    | .inr ⟨_, r', pv⟩  => exact .inr ⟨_, .trans' r r', pv⟩
  case Arr hA _ ih => exact λ v pv ↦ ih (.app r) (p v pv)
  case Prod hA hB _ _ =>
    match p with
    | .inl ⟨_, r', sne⟩ => exact .inl ⟨_, .trans' r r', sne⟩
    | .inr ⟨_, _, r', pm, pn⟩ => exact .inr ⟨_, _, .trans' r r', pm, pn⟩

joint
  theorem 𝒱.adequacy {A P} {v : Val} (h : ⟦ A ⟧ᵛ ↘ P) : (SNeVal v → P v) ∧ (P v → SNVal v)
  theorem 𝒞.adequacy {B P} {m : Com} (h : ⟦ B ⟧ᶜ ↘ P) : (SNeCom m → P m) ∧ (P m → SNCom m)
by
  mutual_induction h, h
  case Unit =>
    refine ⟨λ sne ↦ Or.inl sne, λ sn ↦ ?_⟩
    cases sn
    case inl sne => let ⟨_, e⟩ := sne; subst e; exact .var
    case inr e => subst e; constructor
  case Sum ihl ihr =>
    refine ⟨λ sne ↦ Or.inl sne, λ sne ↦ ?_⟩
    match sne with
    | .inl h => let ⟨_, e⟩ := h; subst e; exact .var
    | .inr (.inl ⟨_, e, pv⟩) => subst e; exact .inl (ihl.right pv)
    | .inr (.inr ⟨_, e, qv⟩) => subst e; exact .inr (ihr.right qv)
  case Pair ihv ihw =>
    refine ⟨λ sne ↦ Or.inl sne, λ sne ↦ ?_⟩
    match sne with
    | .inl h => let ⟨_, e⟩ := h; subst e; exact .var
    | .inr ⟨_, _, e, pv, qw⟩ => subst e; exact .pair (ihv.right pv) (ihw.right qw)
  case U ih =>
    let ⟨sneval, snval⟩ := @ih (force v)
    exact ⟨λ sne ↦ sneval (.force sne),
           λ sn ↦ (snval sn).force_inv⟩
  case F ih =>
    refine ⟨λ sne ↦ Or.inl ⟨_, .refl, sne⟩, λ sn ↦ ?_⟩
    match sn with
    | .inl ⟨_, r, sne⟩ => exact r.red (.ne sne)
    | .inr ⟨_, r, pv⟩  => exact r.red (.ret (ih.right pv))
  case Arr ihv ihm =>
    refine ⟨λ sne ↦ ?sne, λ sn ↦ ?sn⟩
    case sne =>
      exact λ v pv ↦ ihm.left (.app sne (ihv.right pv))
    case sn =>
      exact extensionality (ihm.right (sn (var 0) (ihv.left .var)))
  case Prod ihm ihn =>
    refine ⟨λ sne ↦ ?sne, λ sn ↦ ?sn⟩
    case sne m => exact .inl ⟨_, .refl, sne⟩
    case sn =>
      match sn with
      | .inl ⟨_, r, sne⟩ => refine r.red (.ne sne)
      | .inr ⟨_, _, r, pm, pn⟩ => exact r.red (.prod (ihm.right pm) (ihn.right pn))

def 𝒱.sneVal {A P v} (h : ⟦ A ⟧ᵛ ↘ P) : SNeVal v → P v := h.adequacy.left
def 𝒞.sneCom {B P m} (h : ⟦ B ⟧ᶜ ↘ P) : SNeCom m → P m := h.adequacy.left
def 𝒱.snVal {A P v} (h : ⟦ A ⟧ᵛ ↘ P) : P v → SNVal v := h.adequacy.right
def 𝒞.snCom {B P m} (h : ⟦ B ⟧ᶜ ↘ P) : P m → SNCom m := h.adequacy.right
