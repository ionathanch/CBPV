import CBPV.Evaluation
import CBPV.Typing

open Nat Val Com

/-*------------------------------------------------
  Well-scopedness with respect to jump variables:
  * ScopeComJ δ m says that the jump variables
    in m are bounded by δ (jump context length)
  * ScopeValJ v helps assert that any thunks in v
    are closed wrt jump variables
------------------------------------------------*-/

mutual
inductive ScopeValJ : Val → Prop where
  | var {x} : ScopeValJ (var x)
  | unit : ScopeValJ unit
  | inl {v} : ScopeValJ v → ScopeValJ (inl v)
  | inr {v} : ScopeValJ v → ScopeValJ (inr v)
  | thunk {m} : ScopeComJ 0 m → ScopeValJ (thunk m)

inductive ScopeComJ : Nat → Com → Prop where
  | force {δ v} : ScopeValJ v → ScopeComJ δ (force v)
  | lam {δ m} : ScopeComJ 0 m → ScopeComJ δ (lam m)
  | app {δ m v} : ScopeComJ 0 m → ScopeValJ v → ScopeComJ δ (app m v)
  | ret {δ v} : ScopeValJ v → ScopeComJ δ (ret v)
  | letin {δ m n} : ScopeComJ 0 m → ScopeComJ δ n → ScopeComJ δ (letin m n)
  | case {δ v m n} : ScopeValJ v → ScopeComJ δ m → ScopeComJ δ n → ScopeComJ δ (case v m n)
  | prod {δ m n} : ScopeComJ 0 m → ScopeComJ 0 n → ScopeComJ δ (prod m n)
  | fst {δ m} : ScopeComJ 0 m → ScopeComJ δ (fst m)
  | snd {δ m} : ScopeComJ 0 m → ScopeComJ δ (snd m)
  | join {δ m n} : ScopeComJ δ m → ScopeComJ (δ + 1) n → ScopeComJ δ (join m n)
  | jump {δ j v} : j < δ → ScopeValJ v → ScopeComJ δ (jump j v)
end

@[simp, reducible]
def ScopeSubstJ (σ : Nat → Val) := ∀ x, ScopeValJ (σ x)

/-* Well-typedness implies jump well-scopedness *-/

theorem wtScopeJ {Γ} :
  (∀ {v} {A : ValType}, Γ ⊢ v ∶ A → ScopeValJ v) ∧
  (∀ {Δ m} {B : ComType}, Γ ∣ Δ ⊢ m ∶ B → ScopeComJ (Δ.length) m) := by
  refine ⟨λ hv ↦ ?val, λ hm ↦ ?com⟩
  mutual_induction hv, hm
  all_goals constructor <;> try assumption
  case com.jump mem _ ih => exact Dtxt.inLength mem

theorem ValWt.scopeJ {Γ v} {A : ValType} : Γ ⊢ v ∶ A → ScopeValJ v := wtScopeJ.left
theorem ComWt.scopeJ {Γ Δ m B} : Γ ∣ Δ ⊢ m ∶ B → ScopeComJ (Δ.length) m := wtScopeJ.right

/-* Jump scopes can be weakened *-/

theorem ScopeComJ.weaken {δ δ' m} (h : ScopeComJ δ m) : ScopeComJ (δ + δ') m := by
  mutual_induction h <;> constructor <;> try assumption
  case join ih => rw [Nat.add_right_comm]; exact ih
  case jump ltδ _ => exact Nat.lt_add_right δ' ltδ
theorem ScopeComJ.weaken0 {δ m} (h : ScopeComJ 0 m) : ScopeComJ δ m :=
  by rw [← Nat.zero_add δ]; exact h.weaken

/-* Jump-renaming a computation in an empty jump scope does nothing *-/

@[simp]
def lifts (ξ : Nat → Nat) : Nat → (Nat → Nat)
  | 0 => ξ
  | n + 1 => lift (lifts ξ n)

theorem liftsId {ξ δ j} (ltδ : j < δ) : lifts ξ δ j = j := by
  induction δ generalizing j; contradiction
  case succ ih =>
    cases j <;> simp [lift]
    exact ih (Nat.lt_of_add_lt_add_right ltδ)

theorem renameScopeJ {ξ δ m} (h : ScopeComJ δ m) : renameJCom (lifts ξ δ) m = m := by
  mutual_induction h generalizing ξ <;> simp
  case letin ih => exact ih
  case case ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  case jump ltδ _ => exact liftsId ltδ
  case join ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
theorem renameScopeJ0 {ξ m} : ScopeComJ 0 m → renameJCom ξ m = m := renameScopeJ

/-* Renaming and substitution preserve jump scoping *-/

theorem renameScope {ξ} :
  (∀ {v}, ScopeValJ v → ScopeValJ (renameVal ξ v)) ∧
  (∀ {δ m}, ScopeComJ δ m → ScopeComJ δ (renameCom ξ m)) := by
  refine ⟨λ hv ↦ ?val, λ hm ↦ ?com⟩
  mutual_induction hv, hm generalizing ξ
  all_goals constructor <;> apply_assumption

theorem ScopeSubstJ.lift {σ} (hσ : ScopeSubstJ σ) : ScopeSubstJ (⇑ σ) := by
  intro n; cases n <;> simp [up]; constructor
  case succ n => exact renameScope.left (hσ n)

theorem substScope {σ : Nat → Val} (hσ : ScopeSubstJ σ) :
  (∀ {v}, ScopeValJ v → ScopeValJ (v⦃σ⦄)) ∧
  (∀ {δ m}, ScopeComJ δ m → ScopeComJ δ (m⦃σ⦄)) := by
  refine ⟨λ hv ↦ ?val, λ hm ↦ ?com⟩
  mutual_induction hv, hm generalizing σ
  case var x => exact hσ x
  all_goals constructor <;> try apply_rules [ScopeSubstJ.lift]

theorem ScopeComJ.subst1 {δ m v} (hv : ScopeValJ v) (hm : ScopeComJ δ m) : ScopeComJ δ (m⦃v⦄) := by
  refine (substScope ?_).right hm
  intro n; cases n; exact hv; constructor

theorem Eval.scopeJ {δ m n} (r : m ⇒ n) (h : ScopeComJ δ m) : ScopeComJ δ n := by
  induction r generalizing δ
  case π =>
    cases h with | force h =>
    cases h with | thunk h =>
    exact h.weaken0
  case β =>
    cases h with | app hlam hv =>
    cases hlam with | lam h =>
    exact h.weaken0.subst1 hv
  case ζ =>
    cases h with | letin hret h =>
    cases hret with | ret hv =>
    exact h.subst1 hv
  case ιl =>
    cases h with | case hinl hl hr =>
    cases hinl with | inl hv =>
    exact hl.subst1 hv
  case ιr =>
    cases h with | case hinr hl hr =>
    cases hinr with | inr hv =>
    exact hr.subst1 hv
  case π1 =>
    cases h with | fst h =>
    cases h with | prod h₁ h₂ =>
    exact h₁.weaken0
  case π2 =>
    cases h with | snd h =>
    cases h with | prod h₁ h₂ =>
    exact h₂.weaken0
  case γ =>
    cases h with | join h hjump =>
    cases hjump with | jump _ hv =>
    exact h.subst1 hv
  case ret =>
    cases h with | join _ hret =>
    cases hret with | ret hv =>
    exact .ret hv
  case lam =>
    cases h with | join h₁ h₂ =>
    cases h₂ with | lam h₂ =>
    exact .lam h₂
  case prod =>
    cases h with | join h₁ h₂ =>
    cases h₂ with | prod h₂ h₃ =>
    exact .prod h₂ h₃
  case join't =>
    cases h with | join h₁ h₂ =>
    cases h₂ with | jump ltδ hv =>
    exact .jump (lt_of_succ_lt_succ ltδ) hv
  case app ih =>
    cases h with | app hm hv =>
    exact .app (ih hm) hv
  case letin ih =>
    cases h with | letin h₁ h₂ =>
    exact .letin (ih h₁) h₂
  case fst ih =>
    cases h with | fst h =>
    exact .fst (ih h)
  case snd ih =>
    cases h with | snd h =>
    exact .snd (ih h)
  case join ih =>
    cases h with | join h₁ h₂ =>
    refine .join h₁ (ih h₂)

/-*-----------------------------------------------------------
  Antirenaming: If a jump-renamed m reduces to n,
  then n must be some renamed computation that m reduces to;
  we require that m be well-scoped wrt jump variables.
-----------------------------------------------------------*-/

theorem antirenameJ {ξ δ m n'} (h : ScopeComJ δ m) (r : renameJCom ξ m ⇒ n') :
  ∃ n, n' = renameJCom ξ n ∧ m ⇒ n := by
  generalize e : renameJCom ξ m = m' at r
  induction r generalizing ξ δ m
  case π =>
    cases m <;> injection e
    cases h with | force h =>
    case force m e =>
      cases m <;> injection e
      cases h with | thunk h =>
      case thunk e =>
        subst e; exact ⟨_, (renameScopeJ0 h).symm, .π⟩
  case β =>
    cases m <;> injection e
    cases h with | app h =>
    case app m v em ev _ =>
      cases m <;> injection em
      cases h with | lam h =>
      case lam em =>
        subst em ev; refine ⟨_, ?_, .β⟩
        rw [← renameJSubst, renameScopeJ0 h]
  case ζ =>
    cases m <;> injection e
    case letin m₁ m₂ em₁ em₂ =>
      cases m₁ <;> injection em₁
      case ret v ev =>
        subst ev em₂
        exact ⟨_, renameJSubst ξ (v +: var) m₂, .ζ⟩
  case ιl =>
    cases m <;> injection e
    case case v m₁ m₂ ev em₁ em₂ =>
      cases v <;> injection ev
      case inl v ev =>
        subst ev em₁ em₂
        exact ⟨_, renameJSubst ξ (v +: var) m₁, .ιl⟩
  case ιr =>
    cases m <;> injection e
    case case v m₁ m₂ ev em₁ em₂ =>
      cases v <;> injection ev
      case inr v ev =>
        subst ev em₁ em₂
        exact ⟨_, renameJSubst ξ (v +: var) m₂, .ιr⟩
  case π1 =>
    cases m <;> injection e
    cases h with | fst h =>
    case fst m e =>
      cases m <;> injection e
      cases h with | prod h₁ h₂ =>
      case prod em₁ em₂ =>
        subst em₁ em₂; exact ⟨_, (renameScopeJ0 h₁).symm, .π1⟩
  case π2 =>
    cases m <;> injection e
    cases h with | snd h =>
    case snd m e =>
      cases m <;> injection e
      cases h with | prod h₁ h₂ =>
      case prod em₁ em₂ =>
        subst em₁ em₂; exact ⟨_, (renameScopeJ0 h₂).symm, .π2⟩
  case γ =>
    cases m <;> injection e
    case join m₁ m₂ em₁ em₂ =>
      cases m₂ <;> injection em₂
      case jump j v ej ev =>
        cases j <;> injection ej
        subst ev em₁
        exact ⟨_, renameJSubst ξ (v +: var) m₁, .γ⟩
  case ret =>
    cases m <;> injection e
    case join m₁ m₂ em₁ em₂ =>
      cases m₂ <;> injection em₂
      case ret v ev =>
        subst ev em₁; exact ⟨_, rfl, .ret⟩
  case lam =>
    cases m <;> injection e
    case join m₁ m₂ em₁ em₂ =>
      cases m₂ <;> injection em₂
      case lam m₂ em₂ =>
        subst em₁ em₂; exact ⟨_, rfl, .lam⟩
  case join't =>
    cases m <;> injection e
    case join m₁ m₂ em₁ em₂ =>
      cases m₂ <;> injection em₂
      case jump j v ej ev =>
      cases j <;> injection ej
      case succ j ej =>
        subst ev ej; exact ⟨_, rfl, .join't⟩
  case prod =>
    cases m <;> injection e
    case join m₁ m₂ em₁ em₂ =>
      cases m₂ <;> injection em₂
      case prod n₁ n₂ en₁ en₂ =>
        subst en₁ en₂; exact ⟨_, rfl, .prod⟩
  case app =>
    cases m <;> injection e
    cases h with | app h =>
    case app ih m v em ev _ =>
      subst em ev
      have e : renameJCom ξ m = m := renameScopeJ0 h
      let ⟨n, en, r⟩ := ih h e; subst en
      refine ⟨_, ?_, .app r⟩; simp
      exact renameScopeJ0 (r.scopeJ h)
  case letin =>
    cases m <;> injection e
    cases h with | letin h₁ h₂ =>
    case letin ih m₁ m₂ em₁ em₂ =>
      subst em₁ em₂
      have e : renameJCom ξ m₁ = m₁ := renameScopeJ0 h₁
      let ⟨n, en, r⟩ := ih h₁ e; subst en
      refine ⟨_, ?_, .letin r⟩; simp
      exact renameScopeJ0 (r.scopeJ h₁)
  case fst =>
    cases m <;> injection e
    case fst ih m e =>
      subst e
      cases h with | fst h =>
      have e : renameJCom ξ m = m := renameScopeJ0 h
      let ⟨n, en, r⟩ := ih h e; subst en
      refine ⟨_, ?_, .fst r⟩; simp
      exact renameScopeJ0 (r.scopeJ h)
  case snd =>
    cases m <;> injection e
    case snd ih m e =>
      subst e
      cases h with | snd h =>
      have e : renameJCom ξ m = m := renameScopeJ0 h
      let ⟨n, en, r⟩ := ih h e; subst en
      refine ⟨_, ?_, .snd r⟩; simp
      exact renameScopeJ0 (r.scopeJ h)
  case join =>
    cases m <;> injection e
    case join ih m₁ m₂ em₁ em₂ =>
      subst em₁ em₂
      cases h with | join _ h =>
      let ⟨m₂', em₂, r⟩ := ih h rfl; subst em₂
      exact ⟨_, rfl, .join r⟩
