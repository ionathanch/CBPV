import CBPV.Commutation
import CBPV.CK

open Nat ValType ComType Val Com

/-*-----------------------------------
  A-normal translation continuations
-----------------------------------*-/

inductive K : Nat → Type where
  | nil {δ} : K δ
  | app {δ} : Val → K δ → K δ
  | letin {δ} : Com δ → K δ
  | fst {δ} : K δ → K δ
  | snd {δ} : K δ → K δ

@[simp]
def plug {δ} (n : Com 0) : K δ → Com δ
  | .nil => weakenJCom δ n
  | .app v k => plug (.app n v) k
  | .letin m => .letin n m
  | .fst k => plug (.fst n) k
  | .snd k => plug (.snd n) k
notation:40 k:41 "[" n:41 "]" => plug n k

@[simp]
def renameK {δ} (ξ : Nat → Nat) : K δ → K δ
  | .nil => .nil
  | .app v k => .app (renameVal ξ v) (renameK ξ k)
  | .letin m => .letin (renameCom (lift ξ) m)
  | .fst k => .fst (renameK ξ k)
  | .snd k => .snd (renameK ξ k)

@[simp]
def substK {δ} (σ : Nat → Val) : K δ → K δ
  | .nil => .nil
  | .app v k => .app (substVal σ v) (substK σ k)
  | .letin m => .letin (substCom (⇑ σ) m)
  | .fst k => .fst (substK σ k)
  | .snd k => .snd (substK σ k)

theorem Evals.plug {δ m n} {k : K δ} (r : m ⇒⋆ n) : (k[m]) ⇒⋆ (k[n]) := by
  induction k generalizing m n
  case nil => exact Evals.weakenJ r
  case app ih => exact ih (.app r)
  case letin => exact .letin r
  case fst ih => exact ih (.fst r)
  case snd ih => exact ih (.snd r)

theorem substPlug {δ σ n} {k : K δ} : substCom σ (plug n k) = plug (substCom σ n) (substK σ k) := by
  induction k generalizing n <;> simp
  case nil => rw [weakenJSubst]
  case app ih | fst ih | snd ih => simp [ih]

theorem substRenameK {δ ξ σ} {k : K δ} : substK σ (renameK ξ k) = substK (σ ∘ ξ) k := by
  induction k <;> simp
  case app v _ ih => exact ⟨substRenameVal _ _ v, ih⟩
  case letin m => exact (substRename _ _ _ (upLift _ _ _ (λ _ ↦ rfl))).right m
  case fst ih | snd ih => exact ih

@[simp]
def renameJK {δ δ'} (ξ : Fin δ → Fin δ') : K δ → K δ'
  | .nil => .nil
  | .app v k => .app v (renameJK ξ k)
  | .letin m => .letin (renameJCom ξ m)
  | .fst k => .fst (renameJK ξ k)
  | .snd k => .snd (renameJK ξ k)

/-*--------------------------------------------------
  If a K has the shape
    let x ← k₁[...[kᵢ[□]]] in m,
  return m and the original K with a jump:
    let x ← k₁[...[kᵢ[□]]] in jump 0 x
--------------------------------------------------*-/

inductive Jump : Nat → Type where
  | no {δ} : Jump δ
  | yes {δ} : K (δ + 1) → Com δ → Jump δ

@[simp]
def K.jumpify {δ} : K δ → Jump δ
  | .nil => .no
  | .letin m => .yes (.letin (jump 0 (var 0))) m
  | .app v k =>
    match k.jumpify with
    | .no => .no
    | .yes k' m => .yes (app v k') m
  | .fst k =>
    match k.jumpify with
    | .no => .no
    | .yes k' m => .yes (fst k') m
  | .snd k =>
    match k.jumpify with
    | .no => .no
    | .yes k' m => .yes (snd k') m

theorem Jump.rename {ξ δ k k'} {m : Com δ} (e : k.jumpify = yes k' m) :
  (renameK ξ k).jumpify = yes (renameK ξ k') (renameCom (lift ξ) m) := by
  induction k generalizing k' m
  case nil => cases e
  case letin => simp at *; let ⟨ek, em⟩ := e; subst ek em; simp [lift]
  case app ih | fst ih | snd ih =>
    simp at e; split at e; cases e; injection e with ek em; subst ek em
    case _ e => simp; rw [ih e]

/-*-----------------------------
  A-normal translation of CBPV
-----------------------------*-/

mutual
@[simp]
def Val.joinless : Val → Prop
  | var _ | unit => True
  | inl v | inr v => v.joinless
  | thunk m => m.joinless

@[simp]
def Com.joinless {δ} : Com δ → Prop
  | force v | ret v => v.joinless
  | lam m | fst m | snd m => m.joinless
  | app n v => n.joinless ∧ v.joinless
  | letin m₁ m₂ | prod m₁ m₂ => m₁.joinless ∧ m₂.joinless
  | case v m₁ m₂ => v.joinless ∧ m₁.joinless ∧ m₂.joinless
  | join _ _ | jump _ _ => False
end

section
set_option hygiene false
local notation:1023 "⟦" v "⟧ᵥ" => Aval v
local notation:1023 "⟦" m "⟧ₘ" => Acom .nil (zero_le 0) m
local notation:1022 "⟦" m "⟧ₘ" k "#" le => Acom k le m
mutual
@[simp]
def Aval : Val → Val
  | var x => .var x
  | unit => .unit
  | inl v => .inl ⟦ v ⟧ᵥ
  | inr v => .inr ⟦ v ⟧ᵥ
  | thunk m => .thunk ⟦ m ⟧ₘ

@[simp]
def Acom {δ δ'} (k : K δ) (le : δ' ≤ δ) : Com δ' → Com δ
  | force v => k [ .force ⟦ v ⟧ᵥ ]
  | ret v   => k [ .ret ⟦ v ⟧ᵥ ]
  | lam m   => k [ .lam ⟦ m ⟧ₘ ]
  | app n v   => ⟦ n ⟧ₘ .app ⟦ v ⟧ᵥ k # zero_le δ
  | letin n m => ⟦ n ⟧ₘ .letin (⟦ m ⟧ₘ renameK succ k # le) # zero_le δ
  | prod m₁ m₂ => k [ .prod ⟦ m₁ ⟧ₘ ⟦ m₂ ⟧ₘ ]
  | fst n => ⟦ n ⟧ₘ .fst k # zero_le δ
  | snd n => ⟦ n ⟧ₘ .snd k # zero_le δ
  | join n m => join (⟦ n ⟧ₘ renameK succ k # le)
                     (⟦ m ⟧ₘ renameJK Fin.succ k # succ_le_succ le)
  | jump j v => jump (Fin.castLE le j) (⟦ v ⟧ᵥ)
  | case v m₁ m₂ =>
    match k.jumpify with
    | .no => .case ⟦ v ⟧ᵥ (⟦ m₁ ⟧ₘ renameK succ k # le) (⟦ m₂ ⟧ₘ renameK succ k # le)
    | .yes k m =>
      .join m (.case ⟦ v ⟧ᵥ (⟦ m₁ ⟧ₘ renameK succ k # .step le)
                            (⟦ m₂ ⟧ₘ renameK succ k # .step le))
end
end
notation:1023 "⟦" v "⟧ᵥ" => Aval v
notation:1023 "⟦" m "⟧ₘ" => Acom K.nil (zero_le 0) m
notation:1022 "⟦" m "⟧ₘ" k "#" le => Acom k le m

/-*-----------------------------------------------------------------
  Validity of A-normal translation,
  i.e. translation produces values, computations, configurations:
    v ::= x | () | inl v | inr v | thunk m
    n ::= v! | λx. m | n v | return v | (m, m) | n.1 | n.2
    m ::= n | k[n] | let x ← n in m
      | case v of {inl x => m; inr x => m}
    k ::= □ | k[□ v] | let x ← □ in m | k[fst □] | k[snd □]
-----------------------------------------------------------------*-/

mutual
@[simp]
def isVal : Val → Prop
  | thunk m => isCfg m
  | _ => True

@[simp]
def isCom {δ} : Com δ → Prop
  | force v | ret v => isVal v
  | lam m => isCfg m
  | app n v => isCom n ∧ isVal v
  | fst n | snd n => isCom n
  | prod m₁ m₂ => isCfg m₁ ∧ isCfg m₂
  | _ => False

@[simp]
def isCfg {δ} : Com δ → Prop
  | letin n m => isCom n ∧ isCfg m
  | case _ m₁ m₂ => isCfg m₁ ∧ isCfg m₂
  | join n m => isCfg n ∧ isCfg m
  | jump _ v => isVal v
  | n => isCom n
end

@[simp]
def isK {δ} : K δ → Prop
  | .nil => True
  | .app v k => isVal v ∧ isK k
  | .letin m => isCfg m
  | .fst k | .snd k => isK k

theorem isCom.weakenJ {δ δ'} {n : Com δ} (isc : isCom n) : isCom (weakenJCom δ' n) := by
  mutual_induction n generalizing isc
  all_goals simp at * <;> assumption

theorem isCom.isCfg {δ} {n : Com δ} (isc : isCom n) : isCfg n := by
  mutual_induction n generalizing isc
  case letin | case => unfold isCom at isc; contradiction
  all_goals simp [isc] at *

theorem isK.plug {δ n} {k : K δ} (isk : isK k) (isc : isCom n) : isCfg (k [ n ]) := by
  induction k generalizing n <;> simp at *
  case nil => exact isc.weakenJ.isCfg
  case letin => simp [isk, isc]
  case app ih | fst ih | snd ih => apply ih <;> simp [isk, isc]

theorem isRenameValCfg {ξ} :
  (∀ v, isVal v → isVal (renameVal ξ v)) ∧
  (∀ {δ} (m : Com δ),
    (isCom m → isCom (renameCom ξ m)) ∧
    (isCfg m → isCfg (renameCom ξ m))) := by
  refine ⟨λ v isv ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ
  all_goals simp at *
  case thunk ih => let ⟨_, ih⟩ := @ih ξ; exact ih isv
  case force ih | ret ih => exact ih
  case lam ih => let ⟨_, ih⟩ := @ih (lift ξ); exact ih
  case fst ih | snd ih => let ⟨ih, _⟩ := @ih ξ; exact ih
  case app ihn ihv =>
    intro isn isv
    let ⟨ih, _⟩ := @ihn ξ
    exact ⟨ih isn, ihv isv⟩
  case letin ihn ihm =>
    intro isn ism
    let ⟨ihn, _⟩ := @ihn ξ
    let ⟨_, ihm⟩ := @ihm (lift ξ)
    exact ⟨ihn isn, ihm ism⟩
  case case ihv ihm₁ ihm₂ =>
    intro ism₁ ism₂
    let ⟨_, ihm₁⟩ := @ihm₁ (lift ξ)
    let ⟨_, ihm₂⟩ := @ihm₂ (lift ξ)
    exact ⟨ihm₁ ism₁, ihm₂ ism₂⟩
  case prod ihm₁ ihm₂ =>
    intro ism₁ ism₂
    let ⟨_, ihm₁⟩ := @ihm₁ ξ
    let ⟨_, ihm₂⟩ := @ihm₂ ξ
    exact ⟨ihm₁ ism₁, ihm₂ ism₂⟩
  case join ihn ihm =>
    intro isn ism
    let ⟨_, ihn⟩ := @ihn (lift ξ)
    let ⟨_, ihm⟩ := @ihm ξ
    exact ⟨ihn isn, ihm ism⟩
  case jump ih => exact ih

def isVal.rename {ξ v} : isVal v → isVal (renameVal ξ v) := isRenameValCfg.left v
def isCom.rename {ξ δ} {m : Com δ} : isCom m → isCom (renameCom ξ m) := (isRenameValCfg.right m).left
def isCfg.rename {ξ δ} {m : Com δ} : isCfg m → isCfg (renameCom ξ m) := (isRenameValCfg.right m).right

theorem isCfg.renameJ {δ δ'} {ξ : Fin δ → Fin δ'} : ∀ m, isCfg m → isCfg (renameJCom ξ m) := by
  intro m ism; mutual_induction m generalizing δ' ism
  all_goals simp at *; try assumption
  case letin ih => let ⟨ism, isn⟩ := ism; exact ⟨ism, ih isn⟩
  case case ihm₁ ihm₂ => let ⟨ism₁, ism₂⟩ := ism; exact ⟨ihm₁ ism₁, ihm₂ ism₂⟩
  case join ihn ihm => let ⟨isn, ism⟩ := ism; exact ⟨ihn isn, ihm ism⟩

theorem isK.rename {ξ δ} {k : K δ} (isk : isK k) : isK (renameK ξ k) := by
  induction k generalizing ξ
  all_goals simp at *
  case app ih => let ⟨isv, isk⟩ := isk; exact ⟨isv.rename, ih isk⟩
  case letin => exact isk.rename
  case fst ih | snd ih => exact ih isk

theorem isK.renameJ {δ δ' k} {ξ : Fin δ → Fin δ'} (isk : isK k) : isK (renameJK ξ k) := by
  induction k generalizing ξ
  all_goals simp at *
  case app ih => let ⟨isv, isk⟩ := isk; exact ⟨isv, ih isk⟩
  case letin => exact isk.renameJ
  case fst ih | snd ih => exact ih isk

theorem isK.jumpify {δ k k'} {m : Com δ} (isk : isK k) (e : k.jumpify = .yes k' m) : isK k' ∧ isCfg m := by
  induction k generalizing k' m
  case nil => simp at e
  case letin =>
    injection e with ek em; subst ek em
    simp; exact isk
  case app ih =>
    let ⟨isv, isk⟩ := isk
    simp at e; split at e; cases e
    case _ e' =>
      injection e with ek em; subst ek em
      let ⟨isk, ism⟩ := ih isk e'
      exact ⟨⟨isv, isk⟩, ism⟩
  case fst ih | snd ih =>
    simp at e; split at e; cases e
    case _ e' =>
      injection e with ek em; subst ek em
      let ⟨isk, ism⟩ := ih isk e'
      exact ⟨isk, ism⟩

theorem isANF : (∀ v, isVal ⟦v⟧ᵥ) ∧
  (∀ {δ δ'} (m : Com δ') (k : K δ) (le : δ' ≤ δ), isK k → isCfg (⟦m⟧ₘ k # le)) := by
  refine ⟨λ v ↦ ?val, λ {δ δ'} m k le ↦ ?com⟩
  mutual_induction v, m
  all_goals simp
  case thunk ih => exact ih .nil .refl ⟨⟩
  all_goals intro isk
  case force isv => apply isk.plug; simp [isv]
  case lam ih | ret ih => apply isk.plug; simp [ih]
  case app isc isv => apply isc; simp [isv, isk]
  case letin isc₁ isc₂ => apply isc₁; apply isc₂; simp [isk.rename]
  case prod isc₁ isc₂ => apply isk.plug; simp [isc₁, isc₂]
  case fst isc | snd isc => apply isc; simp [isk]
  case join isc₁ isc₂ => exact ⟨isc₁ _ le (isk.rename), isc₂ _ (succ_le_succ le) isk.renameJ⟩
  case jump ih => exact ih
  case case isc₁ isc₂ =>
    split <;> simp
    case _ => exact ⟨isc₁ _ le (isk.rename), isc₂ _ le (isk.rename)⟩
    case _ e =>
      let ⟨isk, ism⟩ := isk.jumpify e
      exact ⟨ism, isc₁ _ (.step le) (isk.rename), isc₂ _ (.step le) (isk.rename)⟩

def Val.ANF : ∀ v, isVal ⟦v⟧ᵥ := isANF.left
def Com.ANF : ∀ m, isCfg ⟦m⟧ₘ := λ m ↦ isANF.right m .nil .refl ⟨⟩

/-*------------------------------------------
  Type preservation of A-normal translation
  via well-typedness of continuations
------------------------------------------*-/

section
set_option hygiene false
open K
local notation:40 Γ:41 "∣" Δ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => wtK Γ Δ k B₁ B₂
inductive wtK : ∀ {δ}, Ctxt → Dtxt δ → K δ → ComType → ComType → Prop where
  | nil {Γ δ B} {Δ : Dtxt δ} :
    -------------------
    Γ ∣ Δ ⊢ nil ∶ B ⇒ B
  | app {Γ δ Δ v B₁ B₂} {A : ValType} {k : K δ} :
    Γ ⊢ v ∶ A →
    Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂ →
    ---------------------------------
    Γ ∣ Δ ⊢ app v k ∶ (Arr A B₁) ⇒ B₂
  | letin {Γ δ Δ A B} {m : Com δ} :
    Γ ∷ A ∣ Δ ⊢ m ∶ B →
    -------------------------
    Γ ∣ Δ ⊢ letin m ∶ F A ⇒ B
  | fst {Γ δ Δ B₁ B₂ B₃} {k : K δ} :
    Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₃ →
    ---------------------------------
    Γ ∣ Δ ⊢ fst k ∶ (Prod B₁ B₂) ⇒ B₃
  | snd {Γ δ Δ B₁ B₂ B₃} {k : K δ} :
    Γ ∣ Δ ⊢ k ∶ B₂ ⇒ B₃ →
    ---------------------------------
    Γ ∣ Δ ⊢ snd k ∶ (Prod B₁ B₂) ⇒ B₃
end
notation:40 Γ:41 "∣" Δ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => wtK Γ Δ k B₁ B₂

namespace wtK

theorem rename {ξ δ k B₁ B₂} {Γ Ξ : Ctxt} {Δ : Dtxt δ} (hξ : Ξ ⊢ ξ ∶ Γ) (h : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) :
  Ξ ∣ Δ ⊢ renameK ξ k ∶ B₁ ⇒ B₂ := by
  induction h generalizing ξ Ξ
  all_goals constructor <;> apply_rules [wtRenameVal, wtRenameCom, wRenameLift]

theorem weaken {Γ δ Δ A B₁ B₂} {k : K δ} : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∷ A ∣ Δ ⊢ renameK succ k ∶ B₁ ⇒ B₂ :=
  rename wRenameSucc

theorem renameJ {Γ} {δ δ' ξ} {Δ : Dtxt δ} {Φ : Dtxt δ'} {k B₁ B₂} (hξ : Φ ⊢ ξ ∶ Δ) (h : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) :
  Γ ∣ Φ ⊢ renameJK ξ k ∶ B₁ ⇒ B₂ := by
  induction h generalizing δ' Φ
  all_goals constructor <;> apply_rules [wtRenameJ]

theorem weakenJ {Γ δ Δ A B B₁ B₂} {k : K δ} : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∣ Δ ∷ A ↗ B ⊢ renameJK .succ k ∶ B₁ ⇒ B₂ :=
  renameJ wRenameJSucc

theorem plug {Γ δ Δ n B₁ B₂} {k : K δ}
  (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ∣ ⬝ ⊢ n ∶ B₁) : Γ ∣ Δ ⊢ (k [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => exact wtRenameJ (λ _ _ _ mem ↦ by cases mem) h
  case app hv _ hn => simp; exact hn (.app h hv)
  case letin hm => exact .letin h hm
  case fst hn => exact hn (.fst h)
  case snd hn => exact hn (.snd h)

theorem jumpify {Γ δ Δ k' m B₁ B₂} {k : K δ}
  (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (e : k.jumpify = .yes k' m) :
  ∃ A, Γ ∣ Δ ∷ A ↗ B₂ ⊢ k' ∶ B₁ ⇒ B₂ ∧ Γ ∷ A ∣ Δ ⊢ m ∶ B₂ := by
  induction hk
  case nil => cases e
  case letin A _ _ hm =>
    simp at e; let ⟨ek, em⟩ := e; subst ek em
    exact ⟨A, .letin (.jump .here (.var .here)) , hm⟩
  case app hv _ ih | fst ih | snd ih =>
    simp at e; split at e; cases e
    case _ e' =>
      injection e with ek em; subst ek em
      let ⟨A, hk, hm⟩ := ih e'
      refine ⟨A, ?_, hm⟩
      all_goals constructor <;> assumption

end wtK

theorem preservation {Γ} :
  (∀ {v} {A : ValType}, v.joinless → Γ ⊢ v ∶ A → Γ ⊢ ⟦ v ⟧ᵥ ∶ A) ∧
  (∀ {δ δ'} {Δ : Dtxt δ} {Δ' : Dtxt δ'} {k m} {B₁ B₂ : ComType} le, m.joinless → Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∣ Δ' ⊢ m ∶ B₁ → Γ ∣ Δ ⊢ ⟦ m ⟧ₘ k # le ∶ B₂) := by
  refine ⟨λ {v A} vj h ↦ ?val, λ {δ δ' Δ Δ' k m B₁ B₂} le mj hk h ↦ ?com⟩
  mutual_induction h, h
  case var mem => exact .var mem
  case unit => exact .unit
  case inl h => exact .inl (h vj)
  case inr h => exact .inr (h vj)
  case thunk h => exact .thunk (h .refl vj .nil)
  case force h => exact (wtK.plug hk (.force (h mj)))
  case ret h => exact (wtK.plug hk (.ret (h mj)))
  case lam h => exact (wtK.plug hk (.lam (h .refl mj .nil)))
  case app hn hv => let ⟨nj, vj⟩ := mj; exact hn (zero_le δ) nj (.app (hv vj) hk)
  case letin hn hm => let ⟨nj, mj⟩ := mj; exact hn (zero_le δ) nj (.letin (hm le mj (wtK.weaken hk)))
  case prod hm₁ hm₂ => let ⟨mj₁, mj₂⟩ := mj; exact wtK.plug hk (.prod (hm₁ .refl mj₁ .nil) (hm₂ .refl mj₂ .nil))
  case fst h => exact h (zero_le δ) mj (.fst hk)
  case snd h => exact h (zero_le δ) mj (.snd hk)
  case join hn hm | jump mem _ hv => cases mj
  -- let ⟨nj, mj⟩ := mj; exact .join (hn le nj (wtK.weaken hk)) (hm (succ_le_succ le) mj (wtK.weakenJ hk))
  case case hv hm₁ hm₂ =>
    let ⟨vj, mj₁, mj₂⟩ := mj; simp; split
    case _ =>
      exact .case (hv vj) (hm₁ le mj₁ (wtK.weaken hk)) (hm₂ le mj₂ (wtK.weaken hk))
    case _ e =>
      let ⟨_, hk, hm⟩ := hk.jumpify e
      exact (.join hm (.case (hv vj) (hm₁ (.step le) mj₁ (wtK.weaken hk)) (hm₂ (.step le) mj₂ (wtK.weaken hk))))

def ValWt.preservation {Γ} := @(@_root_.preservation Γ).left
def ComWt.preservation {Γ} := @(@_root_.preservation Γ).right

/-*--------------------------------------
  Semantic equivalence of continuations
--------------------------------------*-/

@[simp]
def semK (Γ : Ctxt) {δ} (Δ : Dtxt δ) k₁ k₂ B₁ B₂ :=
  ∀ {σ τ}, Γ ⊨ σ ~ τ →
  ∀ {js₁ js₂}, Δ ⊨ js₁ ~ js₂ →
  ∀ {n₁ n₂}, (n₁, n₂) ∈ ⟦B₁⟧ᵉ →
  (rejoin ((substK σ k₁) [n₁]) js₁, rejoin ((substK τ k₂) [n₂]) js₂) ∈ ⟦B₂⟧ᵉ
notation:40 Γ:41 "∣" Δ:41 "⊨" k₁:41 "~" k₂:41 "∶" B₁:41 "⇒" B₂:41 => semK Γ Δ k₁ k₂ B₁ B₂

namespace semK

theorem weaken {Γ δ} {Δ : Dtxt δ} {k₁ k₂ A B₁ B₂} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ∷ A ∣ Δ ⊨ renameK succ k₁ ~ renameK succ k₂ ∶ B₁ ⇒ B₂ := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn
  rw [substRenameK, substRenameK]
  exact h (semCtxt.rename wRenameSucc hστ) hjs hn

/-*--------------------------------------------------------------
  Fundamental theorem for semantic equivalence of continuations
--------------------------------------------------------------*-/

def nil {Γ δ B} {Δ : Dtxt δ} : Γ ∣ Δ ⊨ .nil ~ .nil ∶ B ⇒ B :=
  λ _ _ _ _ ↦ ℰ.bwdsRejoin .refl .refl

def fst {Γ δ} {Δ : Dtxt δ} {k₁ k₂ B₁ B₂ B₃} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₃) : Γ ∣ Δ ⊨ .fst k₁ ~ .fst k₂ ∶ Prod B₁ B₂ ⇒ B₃ := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn; simp
  have ⟨n₁₁, n₁₂, n₂₁, n₂₂, rn₁, rn₂, hn₁⟩ := hn.fst
  refine ℰ.bwds ?left ?right (h hστ hjs hn₁)
  all_goals refine .rejoin (.plug ?_)
  case left  => rw [← @weakenJCom0 n₁₁]; exact .trans' (Evals.fst rn₁) (.once .π1)
  case right => rw [← @weakenJCom0 n₂₁]; exact .trans' (Evals.fst rn₂) (.once .π1)

def snd {Γ δ} {Δ : Dtxt δ} {k₁ k₂ B₁ B₂ B₃} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₂ ⇒ B₃) : Γ ∣ Δ ⊨ .snd k₁ ~ .snd k₂ ∶ Prod B₁ B₂ ⇒ B₃ := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn; simp
  have ⟨n₁₁, n₁₂, n₂₁, n₂₂, rn₁, rn₂, hn₂⟩ := hn.snd
  refine ℰ.bwds ?left ?right (h hστ hjs hn₂)
  all_goals refine .rejoin (.plug ?_)
  case left  => rw [← @weakenJCom0 n₁₂]; exact .trans' (Evals.snd rn₁) (.once .π2)
  case right => rw [← @weakenJCom0 n₂₂]; exact .trans' (Evals.snd rn₂) (.once .π2)

theorem app {Γ δ} {Δ : Dtxt δ} {v w k₁ k₂ B₁ B₂} {A : ValType} (hA : Γ ⊨ v ~ w ∶ A) (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ∣ Δ ⊨ .app v k₁ ~ .app w k₂ ∶ Arr A B₁ ⇒ B₂ := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn; simp
  have ⟨_, _, rn₁, rn₂, hm⟩ := hn.lam_inv
  refine ℰ.bwds ?left ?right (h hστ hjs (hm _ _ (hA hστ)))
  all_goals refine .rejoin (.plug ?_)
  case left w _ => rw [← @weakenJCom0 (w⦃v⦃σ⦄⦄)]; exact .trans' (Evals.app rn₁) (.once .β)
  case right v  => rw [← @weakenJCom0 (v⦃w⦃τ⦄⦄)]; exact .trans' (Evals.app rn₂) (.once .β)

theorem letin {Γ δ} {Δ : Dtxt δ} {m₁ m₂ A} {B : ComType} (h : Γ ∷ A ∣ Δ ⊨ m₁ ~ m₂ ∶ B) : Γ ∣ Δ ⊨ .letin m₁ ~ .letin m₂ ∶ F A ⇒ B := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn
  have ⟨v, w, rn₁, rn₂, hA⟩ := hn.ret_inv
  refine ℰ.bwds ?_ ?_ (h (semCtxt.cons hA hστ) hjs)
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
  intro σ τ hστ js₁ js₂ hjs; rw [substPlug, substPlug]
  exact hk hστ hjs (hn hστ .nil)

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

theorem semJumpPlug {Γ δ} {Δ : Dtxt δ} {k k' m n B₁ B₂} (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (hn : Γ ∣ ⬝ ⊢ n ∶ B₁) (e : k.jumpify = .yes k' m) :
  Γ ∣ Δ ⊨ (k [ n ]) ~ join m (k' [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => cases e
  case letin hm =>
    simp at e; let ⟨ek, em⟩ := e; subst ek em
    intro σ τ hστ js₁ js₂ hjs
    let ⟨_, _, rn₁, rn₂, hA⟩ := (soundCom hn hστ .nil).ret_inv
    refine ℰ.bwds ?left ?right (soundCom hm (semCtxt.cons hA hστ) hjs)
    all_goals refine .rejoin ?_; rw [← substUnion]
    case left => exact .trans' (Evals.letin rn₁) (.once .ζ)
    case right => exact .trans' (Evals.join (.trans' (Evals.letin rn₂) (.once .ζ))) (.once .γ)
  case app hv _ ih | fst ih | snd ih =>
    simp at e; split at e; cases e; injection e with ek em; subst ek em
    rename _ = _ => e
    refine ih ?_ e; constructor <;> assumption

theorem semJumpA {Γ δ δ'} {Δ : Dtxt δ} {Δ' : Dtxt δ'} {k k' m m' B₁ B₂} (le : δ' ≤ δ) (mj : m.joinless) (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (hm : Γ ∣ Δ' ⊢ m ∶ B₁) (e : k.jumpify = .yes k' m') :
  Γ ∣ Δ ⊨ ⟦m⟧ₘ k # le ~ join m' (⟦m⟧ₘ k' # .step le) ∶ B₂ := by
  mutual_induction hm generalizing δ Δ k k' m' mj
  all_goals intro σ τ
  -- impossible
  case join | jump => cases mj
  -- plugging cases
  case force hv => exact semJumpPlug hk (.force (.preservation mj hv)) e
  case lam hm _ => simp at mj; exact semJumpPlug hk (.lam (.preservation .refl mj .nil hm)) e
  case ret hv => exact semJumpPlug hk (.ret (.preservation mj hv)) e
  case prod hm₁ hm₂ _ _ =>
    let ⟨mj₁, mj₂⟩ := mj
    exact semJumpPlug hk (.prod (.preservation _ mj₁ .nil hm₁) (.preservation _ mj₂ .nil hm₂)) e
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
  case letin Γ _ n m A B hn hm ihn ihm =>
    intro hστ js₁ js₂ hjs; simp
    let ⟨nj, mj⟩ := mj
    have ⟨A', hk', hm'⟩ := wtK.jumpify hk e
    have ahm := ComWt.preservation le mj hk.weaken hm
    have ahn := ComWt.preservation (Δ := Δ ∷ A ↗ B₂) (zero_le (δ + 1)) nj (.letin (.jump .here (.var .here))) hn
    have aihm : Γ ∷ A ∣ Δ ⊨ (⟦ m ⟧ₘ renameK succ k # le) ~ join (renameCom (lift succ) m') (⟦ m ⟧ₘ renameK succ k' # .step le) ∶ B₂ :=
      λ {σ τ} ↦ ihm le mj hk.weaken (Jump.rename e) (σ := σ) (τ := τ)
    have hττ : Γ ⊨ τ ~ τ := semCtxt.trans hστ.sym hστ
    have hjs₂₂ : Δ ⊨ js₂ ~ js₂ := semDtxt.trans hjs.sym hjs
    apply ℰ.trans (ihn (zero_le δ) nj (wtK.letin ahm) rfl hστ hjs)
    apply ℰ.trans (semCom.join aihm (soundCom ahn) hττ hjs₂₂)
    apply ℰ.trans (joinJoin ?_ ?_ ahn hττ hjs₂₂); simp
    rw [← rejoin.eq_2 _ (m'⦃⇑ τ⦄), ← rejoin.eq_2 _ (m'⦃⇑ τ⦄)]
    all_goals sorry
  case case => sorry

/-*-----------------------------------------------------------
  Soundness of A-normal translation wrt semantic equivalence
-----------------------------------------------------------*-/

theorem soundA {Γ} :
  (∀ {v} {A : ValType}, v.joinless → Γ ⊢ v ∶ A → Γ ⊨ v ~ ⟦v⟧ᵥ ∶ A) ∧
  (∀ {δ δ'} {Δ : Dtxt δ} {Δ' : Dtxt δ'} {m k₁ k₂} {B₁ B₂ : ComType} (eq : δ' = 0), m.joinless →
    Γ ∣ Δ' ⊢ m ∶ B₁ → Γ ∣ Δ ⊢ k₁ ∶ B₁ ⇒ B₂ → Γ ∣ Δ ⊢ k₂ ∶ B₁ ⇒ B₂ →
    Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂ → Γ ∣ Δ ⊨ (k₁[cast (congrArg Com eq) m]) ~ ⟦m⟧ₘ k₂ # cast (congrArg (· ≤ δ) eq.symm) (zero_le δ) ∶ B₂) := by
  refine ⟨λ vj h ↦ ?val, λ {δ δ' Δ Δ' m k₁ k₂ B₁ B₂} eq mj h wtk₁ wtk₂ hk ↦ ?com⟩
  mutual_induction h, h
  all_goals intro σ τ; try subst eq
  case force ih _ =>
    refine hk.plug (λ hστ js₁ js₂ _ ↦ ?_)
    cases js₁; cases js₂
    unfold semVal 𝒱 at ih
    let ⟨m, n, h, em, en⟩ := ih mj hστ; simp [em, en]
    refine ℰ.bwd .π .π ?_; simp [weakenJCom0, h]
  case lam ih _ =>
    refine hk.plug (λ hστ js₁ js₂ _ ↦ ?_)
    cases js₁; cases js₂
    refine ℰ.lam (λ v w hA ↦ ?_)
    rw [substUnion, substUnion]
    have goal := ih rfl mj .nil .nil (soundK .nil) (semCtxt.cons hA hστ) .nil
    simp [weakenJCom0] at goal; exact goal
  case app hv ihm ihv _ =>
    let ⟨mj, vj⟩ := mj
    exact ihm rfl mj (.app hv wtk₁) (.app (.preservation vj hv) wtk₂) (semK.app (ihv vj) hk)
  case ret ih _ =>
    refine hk.plug (λ hστ js₁ js₂ _ ↦  ?_)
    cases js₁; cases js₂
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
    refine semCom.trans (semKcase wtk₁ (.case hv hm₁ hm₂)) (λ hστ js₁ js₂ hjs ↦ ?_)
    unfold semVal 𝒱 at ihv
    match ihv vj hστ with
    | .inl ⟨v, w, hA₁, ev, ew⟩ =>
      have hB₂ := ihm₁ rfl mj₁ wtk₁.weaken wtk₂.weaken hk.weaken (semCtxt.cons hA₁ hστ) hjs
      simp; split <;> simp [ev, ew]
      . refine ℰ.bwd (.rejoin .ιl) (.rejoin .ιl) ?_
        rw [substUnion, substUnion]; exact hB₂
      . rename K _ => k'; rename Com _ => m'; rename _ = _ => e
        rw [← rejoin.eq_2]
        refine ℰ.bwd (.rejoin .ιl) (.rejoin .ιl) ?_
        rw [substUnion, substUnion]
        refine ℰ.trans hB₂ ?_
        have goal :=
          semJumpA (zero_le δ) mj₁ wtk₂.weaken hm₁ (Jump.rename e)
            (semCtxt.trans (semCtxt.sym (semCtxt.cons hA₁ hστ)) (semCtxt.cons hA₁ hστ))
            (semDtxt.trans (semDtxt.sym hjs) hjs)
        simp [renameUpSubstCons] at goal; exact goal
    | .inr ⟨v, w, hA₂, ev, ew⟩ =>
      have hB₂ := ihm₂ rfl mj₂ wtk₁.weaken wtk₂.weaken hk.weaken (semCtxt.cons hA₂ hστ) hjs
      simp; split <;> simp [ev, ew]
      . refine ℰ.bwd (.rejoin .ιr) (.rejoin .ιr) ?_
        rw [substUnion, substUnion]; exact hB₂
      . rename K _ => k'; rename Com _ => m'; rename _ = _ => e
        rw [← rejoin.eq_2]
        refine ℰ.bwd (.rejoin .ιr) (.rejoin .ιr) ?_
        rw [substUnion, substUnion]
        refine ℰ.trans hB₂ ?_
        have goal :=
          semJumpA (zero_le δ) mj₂ wtk₂.weaken hm₂ (Jump.rename e)
            (semCtxt.trans (semCtxt.sym (semCtxt.cons hA₂ hστ)) (semCtxt.cons hA₂ hστ))
            (semDtxt.trans (semDtxt.sym hjs) hjs)
        simp [renameUpSubstCons] at goal; exact goal
  case prod ihn₁ ihn₂ _ =>
    let ⟨nj₁, nj₂⟩ := mj
    refine hk.plug (λ hστ js₁ js₂ _ ↦ ?_)
    cases js₁; cases js₂; simp
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

theorem soundAnil {Γ m B} (mj : m.joinless) (h : Γ ∣ ⬝ ⊢ m ∶ B) : Γ ∣ ⬝ ⊨ m ~ ⟦m⟧ₘ ∶ B := by
  intro σ τ hστ js₁ js₂ hjs
  have goal := soundA.right rfl mj h .nil .nil semK.nil hστ hjs
  simp at goal; rw [weakenJCom0] at goal; exact goal

/-*------------------------------------------------------------
  A-normalized ground returners compute the same normal forms
------------------------------------------------------------*-/

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

theorem retGroundA {m n A} (mj : m.joinless) (h : ⬝ ∣ ⬝ ⊢ m ∶ F A) (g : isGround A) (nm : m ⇓ₙ n) : ⟦m⟧ₘ ⇒⋆ n := by
  let ⟨r, nfm⟩ := nm
  let hm := soundAnil mj h semCtxt.nil .nil
  rw [substComId, substComId] at hm
  unfold ℰ 𝒞 at hm
  let ⟨_, _, ⟨r', _⟩, ⟨ra', _⟩, ⟨v₁, v₂, hA, eret₁, eret₂⟩⟩ := hm
  subst eret₁ eret₂; simp at r' ra'
  rw [← hA.ground g] at ra'
  let ⟨_, rn, rret⟩ := confluence r r'
  rw [← rret.ret_inv] at rn
  simp [nfm.steps rn, ra']

theorem retGroundACK {m n A} (mj : m.joinless) (h : ⬝ ∣ ⬝ ⊢ m ∶ F A) (g : isGround A) (nm : nf n) :
  ⟨0, m, .nil⟩ ⤳⋆ ⟨0, n, .nil⟩ → ⟨0, ⟦m⟧ₘ, .nil⟩ ⤳⋆ ⟨0, n, .nil⟩ :=
  λ r ↦ evalStep nm (retGroundA mj h g ⟨stepEvalsNil r, nm⟩)
