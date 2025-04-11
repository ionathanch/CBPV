import CBPV.Normal

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
  | Unit : ⟦ Unit ⟧ᵛ ↘ (λ v ↦ SNeVal v ∨ v ⤳⋆ unit)
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
end
end

notation:40 "⟦" A:41 "⟧ᵛ" "↘" P:41 => 𝒱 A P
notation:40 "⟦" B:41 "⟧ᶜ" "↘" P:41 => 𝒞 B P

theorem interp :
  (∀ A, ∃ P, ⟦ A ⟧ᵛ ↘ P) ∧
  (∀ B, ∃ P, ⟦ B ⟧ᶜ ↘ P) := by
  refine ⟨λ A ↦ ?val, λ B ↦ ?com⟩
  mutual_induction A, B
  case Unit => exact ⟨_, .Unit⟩
  case U ih => let ⟨_, h⟩ := ih; exact ⟨_, .U h⟩
  case F ih => let ⟨_, h⟩ := ih; exact ⟨_, .F h⟩
  case Arr ihA ihB =>
    let ⟨_, hA⟩ := ihA
    let ⟨_, hB⟩ := ihB
    exact ⟨_, .Arr hA hB⟩

def ValType.interp : ∀ A, ∃ P, ⟦ A ⟧ᵛ ↘ P := _root_.interp.left
def ComType.interp : ∀ B, ∃ P, ⟦ B ⟧ᶜ ↘ P := _root_.interp.right

/-*-----------------------------------------------------
  Properties of the logical relation:
  * Interpretation of a type is deterministic
  * Backward closure wrt strong normalization
  * Interpretations contain all strongly neutral terms
  * Terms in interpretations are strongly normalizing
-----------------------------------------------------*-/

theorem determinism :
  (∀ {A P Q}, ⟦ A ⟧ᵛ ↘ P → ⟦ A ⟧ᵛ ↘ Q → P = Q) ∧
  (∀ {B P Q}, ⟦ B ⟧ᶜ ↘ P → ⟦ B ⟧ᶜ ↘ Q → P = Q) := by
  refine ⟨λ {A P Q} h ↦ ?val, λ {B P Q} h ↦ ?com⟩
  mutual_induction h, h
  case Unit => intro h; cases h; rfl
  case U ih =>
    intro h; cases h
    case U hB => rw [ih hB]
  case F ih =>
    intro h; cases h
    case F hA => rw [ih hA]
  case Arr ihA ihB =>
    intro h; cases h
    case Arr hA hB => rw [ihA hA, ihB hB]

def 𝒱.det : ∀ {A P Q}, ⟦ A ⟧ᵛ ↘ P → ⟦ A ⟧ᵛ ↘ Q → P = Q := determinism.left
def 𝒞.det : ∀ {B P Q}, ⟦ B ⟧ᶜ ↘ P → ⟦ B ⟧ᶜ ↘ Q → P = Q := determinism.right

theorem closure :
  (∀ {A P} {v w : Val}, ⟦ A ⟧ᵛ ↘ P → v ⤳⋆ w → P w → P v) ∧
  (∀ {B P} {m n : Com}, ⟦ B ⟧ᶜ ↘ P → m ⤳⋆ n → P n → P m) := by
  refine ⟨λ h ↦ ?val, λ h ↦ ?com⟩
  mutual_induction h, h
  all_goals intro r p
  case Unit =>
    cases p
    case inl h  => exact Or.inl (r.closure h)
    case inr r' => exact Or.inr (.trans' r r')
  case U ih _ _ => exact ih (.force r) p
  case F =>
    match p with
    | .inl ⟨_, r', sne⟩ => exact Or.inl ⟨_, .trans' r r', sne⟩
    | .inr ⟨_, r', pv⟩  => exact Or.inr ⟨_, .trans' r r', pv⟩
  case Arr ih _ _ => exact λ v pv ↦ ih (.app r) (p v pv)

def 𝒱.closure : ∀ {A P} {v w : Val}, ⟦ A ⟧ᵛ ↘ P → v ⤳⋆ w → P w → P v := _root_.closure.left
def 𝒞.closure : ∀ {B P} {m n : Com}, ⟦ B ⟧ᶜ ↘ P → m ⤳⋆ n → P n → P m := _root_.closure.right

theorem adequacy :
  (∀ {A P} {v : Val}, ⟦ A ⟧ᵛ ↘ P → (SNeVal v → P v) ∧ (P v → SNVal v)) ∧
  (∀ {B P} {m : Com}, ⟦ B ⟧ᶜ ↘ P → (SNeCom m → P m) ∧ (P m → SNCom m)) := by
  refine ⟨λ h ↦ ?val, λ h ↦ ?com⟩
  mutual_induction h, h
  case Unit =>
    refine ⟨λ sne ↦ Or.inl sne, λ sn ↦ ?_⟩
    cases sn
    case inl sne => exact .ne sne
    case inr r => rw [r.unit_inv]; constructor
  case U ih v =>
    let ⟨sneval, snval⟩ := @ih (force v)
    exact ⟨λ sne ↦ sneval (.force sne),
           λ sn ↦ (snval sn).force_inv⟩
  case F ih m =>
    refine ⟨λ sne ↦ Or.inl ⟨_, .refl, sne⟩, λ sn ↦ ?_⟩
    match sn with
    | .inl ⟨_, r, sne⟩ => exact r.closure (.ne sne)
    | .inr ⟨_, r, pv⟩  => exact r.closure (.ret (ih.right pv))
  case Arr ihv ihm _ =>
    refine ⟨λ sne ↦ ?sne, λ sn ↦ ?sn⟩
    case sne m =>
      exact λ v pv ↦ ihm.left (.app sne (ihv.right pv))
    case sn =>
      exact extensionality (ihm.right (sn (var 0) (ihv.left .var)))

def 𝒱.sneVal {A P v} (h : ⟦ A ⟧ᵛ ↘ P) : SNeVal v → P v := (adequacy.left h).left
def 𝒞.sneCom {B P m} (h : ⟦ B ⟧ᶜ ↘ P) : SNeCom m → P m := (adequacy.right h).left
def 𝒱.snVal {A P v} (h : ⟦ A ⟧ᵛ ↘ P) : P v → SNVal v := (adequacy.left h).right
def 𝒞.snCom {B P m} (h : ⟦ B ⟧ᶜ ↘ P) : P m → SNCom m := (adequacy.right h).right
