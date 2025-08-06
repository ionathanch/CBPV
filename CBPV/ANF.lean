import CBPV.Commutation
import CBPV.CK

open Nat ValType ComType Val Com

/-*-----------------------------------
  A-normal translation continuations
-----------------------------------*-/

inductive K : Type where
  | nil : K
  | app : Val → K → K
  | letin : Com → K
  | fst : K → K
  | snd : K → K

@[simp]
def plug (n : Com) : K → Com
  | .nil => n
  | .app v k => plug (.app n v) k
  | .letin m => .letin n m
  | .fst k => plug (.fst n) k
  | .snd k => plug (.snd n) k
notation:40 k:41 "[" n:41 "]" => plug n k

@[simp]
def renameK (ξ : Nat → Nat) : K → K
  | .nil => .nil
  | .app v k => .app (renameVal ξ v) (renameK ξ k)
  | .letin m => .letin (renameCom (lift ξ) m)
  | .fst k => .fst (renameK ξ k)
  | .snd k => .snd (renameK ξ k)

@[simp]
def substK (σ : Nat → Val) : K → K
  | .nil => .nil
  | .app v k => .app (substVal σ v) (substK σ k)
  | .letin m => .letin (substCom (⇑ σ) m)
  | .fst k => .fst (substK σ k)
  | .snd k => .snd (substK σ k)

theorem Evals.plug {k m n} (r : m ⇒⋆ n) : (k[m]) ⇒⋆ (k[n]) := by
  induction k generalizing m n
  case nil => exact r
  case app ih => exact ih (.app r)
  case letin => exact .letin r
  case fst ih => exact ih (.fst r)
  case snd ih => exact ih (.snd r)

theorem substPlug {σ n k} : substCom σ (plug n k) = plug (substCom σ n) (substK σ k) := by
  induction k generalizing n <;> simp
  case app ih | fst ih | snd ih => simp [ih]

theorem substRenameK {ξ σ k} : substK σ (renameK ξ k) = substK (σ ∘ ξ) k := by
  induction k <;> simp
  case app v _ ih => exact ⟨substRenameVal _ _ v, ih⟩
  case letin m => exact (substRename _ _ _ (upLift _ _ _ (λ _ ↦ rfl))).right m
  case fst ih | snd ih => exact ih

@[simp]
def renameJK (ξ : Nat → Nat) : K → K
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

inductive JumpK : Type where
  | no : JumpK
  | yes : K → Com → JumpK

@[simp]
def K.jumpify : K → JumpK
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

theorem JumpK.rename {ξ k k' m} (e : k.jumpify = yes k' m) : (renameK ξ k).jumpify = yes (renameK ξ k') (renameCom (lift ξ) m) := by
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
def Com.joinless : Com → Prop
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
local notation:1023 "⟦" m "⟧ₘ" => Acom .nil m
local notation:1022 "⟦" m "⟧ₘ" k => Acom k m
mutual
@[simp]
def Aval : Val → Val
  | var x => .var x
  | unit => .unit
  | inl v => .inl ⟦ v ⟧ᵥ
  | inr v => .inr ⟦ v ⟧ᵥ
  | thunk m => .thunk ⟦ m ⟧ₘ

@[simp]
def Acom (k : K) : Com → Com
  | force v => k [ .force ⟦ v ⟧ᵥ ]
  | ret v   => k [ .ret ⟦ v ⟧ᵥ ]
  | lam m   => k [ .lam ⟦ m ⟧ₘ ]
  | app n v   => ⟦ n ⟧ₘ .app ⟦ v ⟧ᵥ k
  | letin n m => ⟦ n ⟧ₘ .letin (⟦ m ⟧ₘ renameK succ k)
  | prod m₁ m₂ => k [ .prod ⟦ m₁ ⟧ₘ ⟦ m₂ ⟧ₘ ]
  | fst n => ⟦ n ⟧ₘ .fst k
  | snd n => ⟦ n ⟧ₘ .snd k
  | join n m => join (⟦ n ⟧ₘ renameK succ k) (⟦ m ⟧ₘ renameJK succ k)
  | jump j v => jump j (⟦ v ⟧ᵥ)
  | case v m₁ m₂ =>
    match k.jumpify with
    | .no => .case ⟦ v ⟧ᵥ (⟦ m₁ ⟧ₘ renameK succ k) (⟦ m₂ ⟧ₘ renameK succ k)
    | .yes k m => .join m (.case ⟦ v ⟧ᵥ (⟦ m₁ ⟧ₘ renameK succ k) (⟦ m₂ ⟧ₘ renameK succ k))
end
end
notation:1023 "⟦" v "⟧ᵥ" => Aval v
notation:1023 "⟦" m "⟧ₘ" => Acom K.nil m
notation:1022 "⟦" m "⟧ₘ" k => Acom k m

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
def isCom : Com → Prop
  | force v | ret v => isVal v
  | lam m => isCfg m
  | app n v => isCom n ∧ isVal v
  | fst n | snd n => isCom n
  | prod m₁ m₂ => isCfg m₁ ∧ isCfg m₂
  | _ => False

@[simp]
def isCfg : Com → Prop
  | letin n m => isCom n ∧ isCfg m
  | case _ m₁ m₂ => isCfg m₁ ∧ isCfg m₂
  | join n m => isCfg n ∧ isCfg m
  | jump _ v => isVal v
  | n => isCom n
end

@[simp]
def isK : K → Prop
  | .nil => True
  | .app v k => isVal v ∧ isK k
  | .letin m => isCfg m
  | .fst k | .snd k => isK k

theorem isCom.isCfg {n} (isc : isCom n) : isCfg n := by
  mutual_induction n generalizing isc
  case letin | case => unfold isCom at isc; contradiction
  all_goals simp [isc] at *

theorem isK.plug {n k} (isk : isK k) (isc : isCom n) : isCfg (k [ n ]) := by
  induction k generalizing n <;> simp at *
  case nil => exact isc.isCfg
  case letin => simp [isk, isc]
  case app ih | fst ih | snd ih => apply ih <;> simp [isk, isc]

theorem isRenameValCfg {ξ} :
  (∀ v, isVal v → isVal (renameVal ξ v)) ∧
  (∀ m, (isCom m → isCom (renameCom ξ m)) ∧
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
def isCom.rename {ξ m} : isCom m → isCom (renameCom ξ m) := (isRenameValCfg.right m).left
def isCfg.rename {ξ m} : isCfg m → isCfg (renameCom ξ m) := (isRenameValCfg.right m).right

theorem isCfg.renameJ {ξ} : ∀ m, isCfg m → isCfg (renameJCom ξ m) := by
  intro m ism; mutual_induction m generalizing ξ ism
  all_goals simp at *; try assumption
  case letin ih => let ⟨ism, isn⟩ := ism; exact ⟨ism, ih isn⟩
  case case ihm₁ ihm₂ => let ⟨ism₁, ism₂⟩ := ism; exact ⟨ihm₁ ism₁, ihm₂ ism₂⟩
  case join ihn ihm => let ⟨isn, ism⟩ := ism; exact ⟨ihn isn, ihm ism⟩

theorem isK.rename {ξ k} (isk : isK k) : isK (renameK ξ k) := by
  induction k generalizing ξ
  all_goals simp at *
  case app ih => let ⟨isv, isk⟩ := isk; exact ⟨isv.rename, ih isk⟩
  case letin => exact isk.rename
  case fst ih | snd ih => exact ih isk

theorem isK.renameJ {ξ k} (isk : isK k) : isK (renameJK ξ k) := by
  induction k generalizing ξ
  all_goals simp at *
  case app ih => let ⟨isv, isk⟩ := isk; exact ⟨isv, ih isk⟩
  case letin => exact isk.renameJ
  case fst ih | snd ih => exact ih isk

theorem isK.jumpify {k k' m} (isk : isK k) (e : k.jumpify = .yes k' m) : isK k' ∧ isCfg m := by
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

theorem isANF : (∀ v, isVal ⟦v⟧ᵥ) ∧ (∀ m k, isK k → isCfg (⟦m⟧ₘ k)) := by
  refine ⟨λ v ↦ ?val, λ m k ↦ ?com⟩
  mutual_induction v, m
  all_goals simp
  case thunk ih => exact ih _ ⟨⟩
  all_goals intro isk
  case force isv => apply isk.plug; simp [isv]
  case lam ih | ret ih => apply isk.plug; simp [ih]
  case app isc isv => apply isc; simp [isv, isk]
  case letin isc₁ isc₂ => apply isc₁; apply isc₂; simp [isk.rename]
  case prod isc₁ isc₂ => apply isk.plug; simp [isc₁, isc₂]
  case fst isc | snd isc => apply isc; simp [isk]
  case join isc₁ isc₂ => exact ⟨isc₁ _ (isk.rename), isc₂ _ isk.renameJ⟩
  case jump ih => exact ih
  case case isc₁ isc₂ =>
    split <;> simp
    case _ => exact ⟨isc₁ _ (isk.rename), isc₂ _ (isk.rename)⟩
    case _ e =>
      let ⟨isk, ism⟩ := isk.jumpify e
      exact ⟨ism, isc₁ _ (isk.rename), isc₂ _ (isk.rename)⟩

def Val.ANF : ∀ v, isVal ⟦v⟧ᵥ := isANF.left
def Com.ANF : ∀ m, isCfg ⟦m⟧ₘ := λ m ↦ isANF.right m .nil ⟨⟩

/-*------------------------------------------
  Type preservation of A-normal translation
  via well-typedness of continuations
------------------------------------------*-/

section
set_option hygiene false
open K
local notation:40 Γ:41 "∣" Δ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => wtK Γ Δ k B₁ B₂
inductive wtK : Ctxt → Dtxt → K → ComType → ComType → Prop where
  | nil {Γ B} :
    ---------------
    Γ ∣ ⬝ ⊢ nil ∶ B ⇒ B
  | app {Γ Δ k v B₁ B₂} {A : ValType} :
    Γ ⊢ v ∶ A →
    Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂ →
    -----------------------------
    Γ ∣ Δ ⊢ app v k ∶ (Arr A B₁) ⇒ B₂
  | letin {Γ Δ m A} {B : ComType} :
    Γ ∷ A ∣ Δ ⊢ m ∶ B →
    ---------------------
    Γ ∣ Δ ⊢ letin m ∶ F A ⇒ B
  | fst {Γ Δ k B₁ B₂ B₃} :
    Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₃ →
    -----------------------------
    Γ ∣ Δ ⊢ fst k ∶ (Prod B₁ B₂) ⇒ B₃
  | snd {Γ Δ k B₁ B₂ B₃} :
    Γ ∣ Δ ⊢ k ∶ B₂ ⇒ B₃ →
    -----------------------------
    Γ ∣ Δ ⊢ snd k ∶ (Prod B₁ B₂) ⇒ B₃
end
notation:40 Γ:41 "∣" Δ:41 "⊢" k:41 "∶" B₁:41 "⇒" B₂:41 => wtK Γ Δ k B₁ B₂

theorem wtK.rename {ξ k B₁ B₂} {Γ Ξ : Ctxt} {Δ} (hξ : Ξ ⊢ ξ ∶ Γ) (h : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) :
  Ξ ∣ Δ ⊢ renameK ξ k ∶ B₁ ⇒ B₂ := by
  induction h generalizing ξ Ξ
  all_goals constructor <;> apply_rules [wtRenameVal, wtRenameCom, wRenameLift]

theorem wtK.weaken {Γ Δ k A B₁ B₂} : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∷ A ∣ Δ ⊢ renameK succ k ∶ B₁ ⇒ B₂ :=
  wtK.rename wRenameSucc

theorem wtK.plug {Γ Δ n k B₁ B₂}
  (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ∣ ⬝ ⊢ n ∶ B₁) : Γ ∣ Δ ⊢ (k [ n ]) ∶ B₂ := by
  induction hk generalizing n
  case nil => exact h
  case app hv _ hn => simp; exact hn (.app h hv)
  case letin hm => exact .letin h hm
  case fst hn => exact hn (.fst h)
  case snd hn => exact hn (.snd h)

theorem wtK.jumpify {Γ Δ k k' m B₁ B₂}
  (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (e : k.jumpify = .yes k' m) :
  ∃ A, Γ ∣ Δ ∷ A ↗ B₂ ⊢ k' ∶ B₁ ⇒ B₂ ∧ Γ ∷ A ∣ Δ ⊢ m ∶ B₂ := by
  induction hk generalizing k' m
  case nil => cases e
  case letin A _ hm =>
    simp at e; let ⟨ek, em⟩ := e; subst ek em
    exact ⟨A, .letin (.jump .here (.var .here)) , hm⟩
  case app hv _ ih | fst ih | snd ih =>
    simp at e; split at e; cases e
    case _ e' =>
      injection e with ek em; subst ek em
      let ⟨A, hk, hm⟩ := ih e'
      refine ⟨A, ?_, hm⟩
      all_goals constructor <;> assumption

theorem preservation {Γ} :
  (∀ {v} {A : ValType}, v.joinless → Γ ⊢ v ∶ A → Γ ⊢ ⟦ v ⟧ᵥ ∶ A) ∧
  (∀ {Δ k m} {B₁ B₂ : ComType}, m.joinless → Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂ → Γ ∣ ⬝ ⊢ m ∶ B₁ → Γ ∣ Δ ⊢ ⟦ m ⟧ₘ k ∶ B₂) := by
  refine ⟨λ vj h ↦ ?val, λ mj hk h ↦ ?com⟩
  case' com => generalize e : Dtxt.nil = Δ' at h
  mutual_induction h, h
  case var mem => exact .var mem
  case unit => exact .unit
  case inl h => exact .inl (h vj)
  case inr h => exact .inr (h vj)
  case thunk h => exact .thunk (h vj .nil rfl)
  all_goals subst e
  case force h _ _ _ => exact (wtK.plug hk (.force (h mj)))
  case ret h _ _ _ => exact (wtK.plug hk (.ret (h mj)))
  case lam h _ _ _ => exact (wtK.plug hk (.lam (h mj .nil rfl)))
  case app hn hv k _ _ => let ⟨nj, vj⟩ := mj; exact hn nj (.app (hv vj) hk) rfl
  case letin hn _ _ _ _ hm => let ⟨nj, mj⟩ := mj; exact hn nj (.letin (hm mj (wtK.weaken hk) rfl)) rfl
  case prod hm₁ hm₂ _ _ _ => let ⟨mj₁, mj₂⟩ := mj; exact wtK.plug hk (.prod (hm₁ mj₁ .nil rfl) (hm₂ mj₂ .nil rfl))
  case fst h _ _ _ => exact h mj (.fst hk) rfl
  case snd h _ _ _ => exact h mj (.snd hk) rfl
  case join | jump => simp at mj
  case case hv _ _ _ _ _ hm₁ hm₂ =>
    let ⟨vj, mj₁, mj₂⟩ := mj; simp; split
    case _ =>
      exact .case (hv vj) (hm₁ mj₁ (wtK.weaken hk) rfl) (hm₂ mj₂ (wtK.weaken hk) rfl)
    case _ e =>
      let ⟨_, hk, hm⟩ := hk.jumpify e
      exact (.join hm (.case (hv vj) (hm₁ mj₁ (wtK.weaken hk) rfl) (hm₂ mj₂ (wtK.weaken hk) rfl)))

/-*--------------------------------------
  Semantic equivalence of continuations
--------------------------------------*-/

@[simp]
def semK (Γ : Ctxt) (Δ : Dtxt) k₁ k₂ B₁ B₂ :=
  ∀ {σ τ}, Γ ⊨ σ ~ τ →
  ∀ {js₁ js₂}, Δ ⊨ js₁ ~ js₂ →
  ∀ {n₁ n₂}, (n₁, n₂) ∈ ⟦B₁⟧ᵉ →
  (rejoin ((substK σ k₁) [n₁]) js₁, rejoin ((substK τ k₂) [n₂]) js₂) ∈ ⟦B₂⟧ᵉ
notation:40 Γ:41 "∣" Δ:41 "⊨" k₁:41 "~" k₂:41 "∶" B₁:41 "⇒" B₂:41 => semK Γ Δ k₁ k₂ B₁ B₂

namespace semK

theorem weaken {Γ Δ k₁ k₂ A B₁ B₂} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ∷ A ∣ Δ ⊨ renameK succ k₁ ~ renameK succ k₂ ∶ B₁ ⇒ B₂ := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn
  rw [substRenameK, substRenameK]
  exact h (semCtxt.rename wRenameSucc hστ) hjs hn

/-*--------------------------------------------------------------
  Fundamental theorem for semantic equivalence of continuations
--------------------------------------------------------------*-/

def nil {Γ Δ B} : Γ ∣ Δ ⊨ .nil ~ .nil ∶ B ⇒ B :=
  λ _ _ _ _ ↦ ℰ.bwdsRejoin .refl .refl

def fst {Γ Δ k₁ k₂ B₁ B₂ B₃} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₃) : Γ ∣ Δ ⊨ .fst k₁ ~ .fst k₂ ∶ Prod B₁ B₂ ⇒ B₃ := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn; simp
  have ⟨n₁₁, n₁₂, n₂₁, n₂₂, rn₁, rn₂, hn₁⟩ := hn.fst
  refine ℰ.bwds ?_ ?_ (h hστ hjs hn₁)
  all_goals refine .rejoin (.plug ?_)
  . exact .trans' (Evals.fst rn₁) (.once .π1)
  . exact .trans' (Evals.fst rn₂) (.once .π1)

def snd {Γ Δ k₁ k₂ B₁ B₂ B₃} (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₂ ⇒ B₃) : Γ ∣ Δ ⊨ .snd k₁ ~ .snd k₂ ∶ Prod B₁ B₂ ⇒ B₃ := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn; simp
  have ⟨n₁₁, n₁₂, n₂₁, n₂₂, rn₁, rn₂, hn₂⟩ := hn.snd
  refine ℰ.bwds ?_ ?_ (h hστ hjs hn₂)
  all_goals refine .rejoin (.plug ?_)
  . exact .trans' (Evals.snd rn₁) (.once .π2)
  . exact .trans' (Evals.snd rn₂) (.once .π2)

theorem app {Γ Δ v w k₁ k₂ B₁ B₂} {A : ValType} (hA : Γ ⊨ v ~ w ∶ A) (h : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) : Γ ∣ Δ ⊨ .app v k₁ ~ .app w k₂ ∶ Arr A B₁ ⇒ B₂ := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn; simp
  have ⟨_, _, rn₁, rn₂, hm⟩ := hn.lam_inv
  refine ℰ.bwds ?_ ?_ (h hστ hjs (hm _ _ (hA hστ)))
  all_goals refine .rejoin (.plug ?_)
  . exact .trans' (Evals.app rn₁) (.once .β)
  . exact .trans' (Evals.app rn₂) (.once .β)

theorem letin {Γ Δ m₁ m₂ A} {B : ComType} (h : Γ ∷ A ∣ Δ ⊨ m₁ ~ m₂ ∶ B) : Γ ∣ Δ ⊨ .letin m₁ ~ .letin m₂ ∶ F A ⇒ B := by
  intro σ τ hστ js₁ js₂ hjs n₁ n₂ hn
  have ⟨v, w, rn₁, rn₂, hA⟩ := hn.ret_inv
  refine ℰ.bwds ?_ ?_ (h (semCtxt.cons hA hστ) hjs)
  all_goals rw [← substUnion]; refine .rejoin ?_
  . exact .trans' (Evals.letin rn₁) (.once .ζ)
  . exact .trans' (Evals.letin rn₂) (.once .ζ)

end semK

theorem soundK {Γ Δ k B₁ B₂} (h : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) : Γ ∣ Δ ⊨ k ~ k ∶ B₁ ⇒ B₂ := by
  induction h
  case nil => exact semK.nil
  case app hv _ ih => exact semK.app (soundVal hv) ih
  case letin hm => exact semK.letin (soundCom hm)
  case fst ih => exact semK.fst ih
  case snd ih => exact semK.snd ih

/-*----------------------------------------------
  Semantic equivalence of plugged continuations
----------------------------------------------*-/

theorem semK.plug {Γ Δ n₁ n₂ k₁ k₂ B₁ B₂} (hk : Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂) (hn : Γ ∣ ⬝ ⊨ n₁ ~ n₂ ∶ B₁) : Γ ∣ Δ ⊨ (k₁[n₁]) ~ (k₂[n₂]) ∶ B₂ := by
  intro σ τ hστ js₁ js₂ hjs; rw [substPlug, substPlug]
  exact hk hστ hjs (hn hστ .nil)

theorem semPlug {Γ Δ n₁ n₂ k B₁ B₂} (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (hn : Γ ∣ ⬝ ⊨ n₁ ~ n₂ ∶ B₁) : Γ ∣ Δ ⊨ (k [ n₁ ]) ~ (k [ n₂ ]) ∶ B₂ :=
  semK.plug (soundK hk) hn

/-*--------------------------------------
  Plugging commutes with configurations
--------------------------------------*-/

theorem semKletin {Γ Δ n m k B₁ B₂} (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ∣ ⬝ ⊢ letin n m ∶ B₁) :
  Γ ∣ Δ ⊨ (k [letin n m]) ~ letin n ((renameK succ k) [m]) ∶ B₂ := by
  induction hk generalizing n m
  case nil => exact soundCom h
  case app hv hk ih => exact semCom.trans (semPlug hk (appLet h hv)) (ih (wtLetApp h hv))
  case letin hm => exact letLet h hm
  case fst hk ih => exact semCom.trans (semPlug hk (fstLet h)) (ih (wtLetFst h))
  case snd hk ih => exact semCom.trans (semPlug hk (sndLet h)) (ih (wtLetSnd h))

theorem semKcase {Γ Δ v m₁ m₂ k B₁ B₂} (hk : Γ ∣ Δ ⊢ k ∶ B₁ ⇒ B₂) (h : Γ ∣ ⬝ ⊢ case v m₁ m₂ ∶ B₁) :
  Γ ∣ Δ ⊨ (k [case v m₁ m₂]) ~ case v ((renameK succ k) [m₁]) ((renameK succ k) [m₂]) ∶ B₂ := by
  induction hk generalizing v m₁ m₂
  case nil => exact soundCom h
  case app hv hk ih => exact semCom.trans (semPlug hk (appCase h hv)) (ih (wtCaseApp h hv))
  case letin hm => exact letCase h hm
  case fst hk ih => exact semCom.trans (semPlug hk (fstCase h)) (ih (wtCaseFst h))
  case snd hk ih => exact semCom.trans (semPlug hk (sndCase h)) (ih (wtCaseSnd h))

/-*-----------------------------------------------------------
  Soundness of A-normal translation wrt semantic equivalence
-----------------------------------------------------------*-/

theorem soundA {Γ} :
  (∀ {v} {A : ValType}, v.joinless → Γ ⊢ v ∶ A → Γ ⊨ v ~ ⟦v⟧ᵥ ∶ A) ∧
  (∀ {Δ m k₁ k₂} {B₁ B₂ : ComType}, m.joinless → Γ ∣ ⬝ ⊢ m ∶ B₁ → Γ ∣ Δ ⊢ k₁ ∶ B₁ ⇒ B₂ →
    Γ ∣ Δ ⊨ k₁ ~ k₂ ∶ B₁ ⇒ B₂ → Γ ∣ Δ ⊨ (k₁[m]) ~ ⟦m⟧ₘ k₂ ∶ B₂) := by
  refine ⟨λ vj h ↦ ?val, λ mj h wtk hk ↦ ?com⟩
  case' com => generalize e : Dtxt.nil = Δ' at h
  mutual_induction h, h
  all_goals intro σ τ; try subst e
  case force ih _ _ _ _ =>
    refine hk.plug (λ hστ _ _ _ ↦ ?_)
    unfold semVal 𝒱 at ih
    let ⟨_, _, h, em, en⟩ := ih mj hστ
    simp [em, en]; exact ℰ.bwdRejoin .π .π h
  case lam ih _ _ _ _ =>
    refine hk.plug (λ hστ _ _ _ ↦ ℰ.bwdsRejoin .refl .refl (ℰ.lam (λ v w hA ↦ ?_)))
    rw [substUnion, substUnion]
    exact ih mj .nil (soundK .nil) rfl (semCtxt.cons hA hστ) .nil
  case app hv ihm ihv _ k₁ k₂ _ =>
    let ⟨mj, vj⟩ := mj
    exact ihm mj (.app hv wtk) (semK.app (ihv vj) hk) rfl
  case ret ih _ _ _ _ =>
    refine hk.plug (λ hστ _ _ _ ↦  ?_)
    exact ℰ.bwdsRejoin .refl .refl (ℰ.ret (ih mj hστ))
  case letin hn ihn _ _ _ _ hm ihm =>
    let ⟨nj, mj⟩ := mj
    refine semCom.trans (semKletin wtk (.letin hn hm)) ?_
    exact ihn nj
      (.letin (wtk.weaken.plug hm))
      (semK.letin (ihm mj wtk.weaken hk.weaken rfl)) rfl
  case case hv ihv _ _ _ ihm₁ hm₁ hm₂ ihm₁ ihm₂ =>
    let ⟨vj, mj₁, mj₂⟩ := mj
    refine semCom.trans (semKcase wtk (.case hv hm₁ hm₂)) (λ hστ js₁ js₂ hjs ↦ ?_)
    unfold semVal 𝒱 at ihv
    match ihv vj hστ with
    | .inl ⟨v, w, hA₁, ev, ew⟩ =>
      simp [ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm₁ mj₁ wtk.weaken hk.weaken rfl (semCtxt.cons hA₁ hστ) hjs)
      all_goals rw [← substUnion]; exact (.rejoin .ιl)
    | .inr ⟨v, w, hA₂, ev, ew⟩ =>
      simp [ev, ew]
      refine ℰ.bwd ?_ ?_ (ihm₂ mj₂ wtk.weaken hk.weaken rfl (semCtxt.cons hA₂ hστ) hjs)
      all_goals rw [← substUnion]; exact (.rejoin .ιr)
  case prod ihn₁ ihn₂ _ _ _ _ =>
    let ⟨nj₁, nj₂⟩ := mj
    refine hk.plug (λ hστ _ _ _ ↦ ?_)
    exact ℰ.bwdsRejoin .refl .refl
      (ℰ.prod (ihn₁ nj₁ .nil (soundK .nil) rfl hστ .nil)
              (ihn₂ nj₂ .nil (soundK .nil) rfl hστ .nil))
  case fst ih _ _ _ _ => exact ih mj (.fst wtk) (semK.fst hk) rfl
  case snd ih _ _ _ _ => exact ih mj (.snd wtk) (semK.snd hk) rfl
  case join | jump => cases mj
  all_goals intro hστ
  case var mem => exact hστ mem
  case unit => exact 𝒱.unit
  case inl ih => exact 𝒱.inl (ih vj hστ)
  case inr ih => exact 𝒱.inr (ih vj hστ)
  case thunk ih => exact 𝒱.thunk (ih vj .nil (soundK .nil) rfl hστ .nil)

theorem soundAnil {Γ m B} (mj : m.joinless) (h : Γ ∣ ⬝ ⊢ m ∶ B) : Γ ∣ ⬝ ⊨ m ~ ⟦m⟧ₘ ∶ B :=
  soundA.right mj h .nil semK.nil

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
  ⟨m, []⟩ ⤳⋆ ⟨n, []⟩ → ⟨⟦m⟧ₘ, []⟩ ⤳⋆ ⟨n, []⟩ :=
  λ r ↦ evalStep nm (retGroundA mj h g ⟨stepEvalsNil r, nm⟩)
