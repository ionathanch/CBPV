import CBPV.Typing
import CBPV.Evaluation

open Nat ValType ComType Val Com

/-*------------------------------------
  CC-normal translation continuations
------------------------------------*-/

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

theorem renameRenameJK {δ δ' ζ k} {ξ : Fin δ → Fin δ'} : renameJK ξ (renameK ζ k) = renameK ζ (renameJK ξ k) := by
  induction k <;> simp <;> try assumption
  case letin => rw [renameToSubstCom, renameToSubstCom, renameJSubst]

theorem renameJKPlug {δ δ' n} {ξ : Fin δ → Fin δ'} {k : K δ} : renameJCom ξ (k[ n ]) = plug n (renameJK ξ k) := by
  induction k generalizing n <;> simp [renameWeakenJ]
  all_goals apply_assumption

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

theorem Jump.renameJ {δ δ' k k' m} {ξ : Fin δ → Fin δ'} (e : k.jumpify = yes k' m) :
  (renameJK ξ k).jumpify = yes (renameJK (liftJ ξ) k') (renameJCom ξ m) := by
  induction k generalizing k' m
  case nil => cases e
  case letin => simp at *; let ⟨ek, em⟩ := e; subst ek em; simp [liftJ]; rfl
  case app ih | fst ih | snd ih =>
    simp at e; split at e; cases e; injection e with ek em; subst ek em
    case _ e => simp; rw [ih e]

theorem Jump.repeat {δ k' m'} {k : K δ} (e : k.jumpify = yes k' m') : ∃ k'', k'.jumpify = yes k'' (jump 0 (var 0)) := by
  induction k generalizing k' m'
  case nil => cases e
  case letin => injection e with ek' em'; subst ek' em'; simp
  case app ih | fst ih | snd ih =>
    simp at e; split at e; cases e; injection e with ek em; subst ek em
    case _ e => let ⟨_, e⟩ := ih e; simp [e]

/-*------------------------------
  CC-normal translation of CBPV
------------------------------*-/

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
local notation:1023 "⟦" v "⟧ᵥ" => CCval v
local notation:1023 "⟦" m "⟧ₘ" => CCcom .nil (zero_le 0) m
local notation:1022 "⟦" m "⟧ₘ" k "#" le => CCcom k le m
mutual
@[simp]
def CCval : Val → Val
  | var x => .var x
  | unit => .unit
  | inl v => .inl ⟦ v ⟧ᵥ
  | inr v => .inr ⟦ v ⟧ᵥ
  | thunk m => .thunk ⟦ m ⟧ₘ

@[simp]
def CCcom {δ δ'} (k : K δ) (le : δ' ≤ δ) : Com δ' → Com δ
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
    | .no | .yes _ (jump _ _) =>
      .case ⟦ v ⟧ᵥ (⟦ m₁ ⟧ₘ renameK succ k # le) (⟦ m₂ ⟧ₘ renameK succ k # le)
    | .yes k m =>
      .join m (.case ⟦ v ⟧ᵥ (⟦ m₁ ⟧ₘ renameK succ k # .step le)
                            (⟦ m₂ ⟧ₘ renameK succ k # .step le))
end
end
notation:1023 "⟦" v "⟧ᵥ" => CCval v
notation:1023 "⟦" m "⟧ₘ" => CCcom K.nil (zero_le 0) m
notation:1022 "⟦" m "⟧ₘ" k "#" le => CCcom k le m

/-*---------------------------------------------------
  Renaming join points commutes with the translation
---------------------------------------------------*-/

theorem CCcom.renameJ {δ δ' m m' k k' ξ} (le : δ' ≤ δ + 1) (mj : m.joinless) (e : k.jumpify = .yes k' m') :
  renameJCom ξ (⟦ m ⟧ₘ k # le) = ⟦ m ⟧ₘ renameJK ξ k # .step le := by
  mutual_induction m generalizing δ k k' mj ξ
  all_goals try simp [lift]; rfl
  case force | ret | lam | prod => exact renameJKPlug
  case app ih | fst ih | snd ih =>
    apply ih; simp at mj; simp [mj]; simp; rw [e]
  case letin ihn ihm =>
    let ⟨nj, mj⟩ := mj
    simp; rw [← renameRenameJK]
    rw [ihn (zero_le (δ + 1)) nj rfl]
    rw [← ihm le mj (Jump.rename e)]; rfl
  case case ih₁ ih₂ =>
    let ⟨vj, mj₁, mj₂⟩ := mj
    simp; split
    case _ eno => rw [e] at eno; cases eno
    case _ eyes =>
      rw [e] at eyes; cases eyes; rw [Jump.renameJ e]; simp
      simp [← renameRenameJK, ih₁ le mj₁ (Jump.rename e), ih₂ le mj₂ (Jump.rename e)]
    case _ jumpn't eyes =>
      rw [e] at eyes; cases eyes; split
      case _ eno => rw [Jump.renameJ e] at eno; cases eno
      case _ eyes =>
        rw [Jump.renameJ e] at eyes; injection eyes with ek em
        cases m' <;> cases em
        cases jumpn't _ _ rfl
      case _ eyes =>
        rw [Jump.renameJ e] at eyes; cases eyes
        have ⟨_, e⟩ := Jump.repeat e
        simp; rw [← renameRenameJK]
        exact ⟨ih₁ (.step le) mj₁ (Jump.rename e),
               ih₂ (.step le) mj₂ (Jump.rename e)⟩
  case join | jump => cases mj

/-*-----------------------------------------------------------------
  Validity of CC-normal translation,
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

theorem isCCNF : (∀ v, isVal ⟦v⟧ᵥ) ∧
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
    case _ | _ => exact ⟨isc₁ _ le (isk.rename), isc₂ _ le (isk.rename)⟩
    case _ e =>
      let ⟨isk, ism⟩ := isk.jumpify e
      exact ⟨ism, isc₁ _ (.step le) (isk.rename), isc₂ _ (.step le) (isk.rename)⟩

def Val.CCNF : ∀ v, isVal ⟦v⟧ᵥ := isCCNF.left
def Com.CCNF : ∀ m, isCfg ⟦m⟧ₘ := λ m ↦ isCCNF.right m .nil .refl ⟨⟩

/-*-------------------------------------------
  Type preservation of CC-normal translation
  via well-typedness of continuations
-------------------------------------------*-/

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
    case _ | _ =>
      exact .case (hv vj) (hm₁ le mj₁ (wtK.weaken hk)) (hm₂ le mj₂ (wtK.weaken hk))
    case _ e =>
      let ⟨_, hk, hm⟩ := hk.jumpify e
      exact (.join hm (.case (hv vj) (hm₁ (.step le) mj₁ (wtK.weaken hk)) (hm₂ (.step le) mj₂ (wtK.weaken hk))))

def ValWt.preservation {Γ} := @(@_root_.preservation Γ).left
def ComWt.preservation {Γ} := @(@_root_.preservation Γ).right
