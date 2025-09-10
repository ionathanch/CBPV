import MutualInduction

open Nat

@[simp]
def cons {A : Type} (x : A) (ξ : Nat → A) : Nat → A
  | 0 => x
  | n + 1 => ξ n
infixr:50 "+:" => cons

/-*------
  Types
------*-/

mutual
inductive ValType : Type where
  | Unit : ValType
  | Sum : ValType → ValType → ValType
  | U : ComType → ValType

inductive ComType : Type where
  | F : ValType → ComType
  | Arr : ValType → ComType → ComType
  | Prod : ComType → ComType → ComType
end
open ValType ComType

/-*------
  Terms
------*-/

mutual
inductive Val : Type where
  | var : Nat → Val
  | unit : Val
  | inl : Val → Val
  | inr : Val → Val
  | thunk : Com → Val

inductive Com : Type where
  | force : Val → Com
  | lam : Com → Com
  | app : Com → Val → Com
  | ret : Val → Com
  | letin : Com → Com → Com
  | case : Val → Com → Com → Com
  | prod : Com → Com → Com
  | fst : Com → Com
  | snd : Com → Com
  | join : Com → Com → Com
  | jump : Nat → Val → Com
end
open Val Com

theorem appCong {m m' v v'} : m = m' → v = v' → app m v = app m' v'
  | rfl, rfl => rfl

theorem letinCong {m m' n n'} : m = m' → n = n' → letin m n = letin m' n'
  | rfl, rfl => rfl

theorem prodCong {m m' n n'} : m = m' → n = n' → prod m n = prod m' n'
  | rfl, rfl => rfl

theorem joinCong {m m' n n'} : m = m' → n = n' → join m n = join m' n'
  | rfl, rfl => rfl

/-*------------------
  Lifting renamings
------------------*-/

def lift (ξ : Nat → Nat) : Nat → Nat :=
  zero +: (succ ∘ ξ)

-- Lifting respects renaming extensionality
theorem liftExt ξ ζ (h : ∀ x, ξ x = ζ x) : ∀ x, lift ξ x = lift ζ x := by
  intro x; cases x <;> simp [lift, h]

-- Lifting identity renaming does nothing
theorem liftId ξ (h : ∀ x, ξ x = x) : ∀ x, lift ξ x = x := by
  intro x; cases x <;> simp [lift, h]

-- Lifting composes
theorem liftComp ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  ∀ x, (lift ξ ∘ lift ζ) x = lift ς x := by
  intro x; cases x <;> simp [lift]
  case succ => apply h

-- Lifting commutes with succ
theorem liftSucc ξ : ∀ x, (lift ξ ∘ succ) x = (succ ∘ ξ) x := by
  intro x; cases x <;> simp [lift]

-- Lifting twice commutes with lifted succ
theorem liftLiftSucc ξ : ∀ (x : Nat), (lift (lift ξ) ∘ lift succ) x = (lift succ ∘ (lift ξ)) x := by
  intro x; cases x <;> simp [lift]

/-*-------------------
  Applying renamings
-------------------*-/

mutual
@[simp]
def renameVal (ξ : Nat → Nat) : Val → Val
  | var s => var (ξ s)
  | unit => unit
  | inl v => inl (renameVal ξ v)
  | inr v => inr (renameVal ξ v)
  | thunk m => thunk (renameCom ξ m)

@[simp]
def renameCom (ξ : Nat → Nat) : Com → Com
  | force v => force (renameVal ξ v)
  | lam m => lam (renameCom (lift ξ) m)
  | app m v => app (renameCom ξ m) (renameVal ξ v)
  | ret v => ret (renameVal ξ v)
  | letin m n => letin (renameCom ξ m) (renameCom (lift ξ) n)
  | case v m n => case (renameVal ξ v) (renameCom (lift ξ) m) (renameCom (lift ξ) n)
  | prod m n => prod (renameCom ξ m) (renameCom ξ n)
  | fst m => fst (renameCom ξ m)
  | snd m => snd (renameCom ξ m)
  | join m n => join (renameCom (lift ξ) m) (renameCom ξ n)
  | jump j v => jump j (renameVal ξ v)
end

-- Renaming extensionality
theorem renameExt ξ ζ (h : ∀ x, ξ x = ζ x) :
  (∀ v, renameVal ξ v = renameVal ζ v) ∧
  (∀ m, renameCom ξ m = renameCom ζ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ ζ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftExt]

def renameValExt ξ ζ h := (renameExt ξ ζ h).left
def renameComExt ξ ζ h := (renameExt ξ ζ h).right

-- Applying identity renaming does nothing
theorem renameId :
  (∀ v, renameVal id v = v) ∧
  (∀ m, renameCom id m = m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m
  all_goals simp; try repeat' constructor
  all_goals try assumption
  all_goals rw [renameComExt (lift id) id]
  all_goals apply_rules [liftId]

def renameValId := renameId.left
def renameComId := renameId.right

-- Renamings compose
theorem renameComp ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  (∀ v, (renameVal ξ ∘ renameVal ζ) v = renameVal ς v) ∧
  (∀ m, (renameCom ξ ∘ renameCom ζ) m = renameCom ς m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?comp⟩
  mutual_induction v, m generalizing ξ ζ ς
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftComp]

def renameValComp ξ ζ v : renameVal ξ (renameVal ζ v) = renameVal (ξ ∘ ζ) v :=
  (renameComp ξ ζ (ξ ∘ ζ) (λ _ ↦ rfl)).left v

def renameComComp ξ ζ m : renameCom ξ (renameCom ζ m) = renameCom (ξ ∘ ζ) m :=
  (renameComp ξ ζ (ξ ∘ ζ) (λ _ ↦ rfl)).right m

-- Join point renamings
@[simp]
def renameJCom (ξ : Nat → Nat) : Com → Com
  | letin m n => letin m (renameJCom ξ n)
  | case v m n => case v (renameJCom ξ m) (renameJCom ξ n)
  | join n m => join (renameJCom ξ n) (renameJCom (lift ξ) m)
  | jump j v => jump (ξ j) v
  | m => m

/-*----------------------
  Lifting substitutions
----------------------*-/

def up (σ : Nat → Val) : Nat → Val :=
  var 0 +: (renameVal succ ∘ σ)
prefix:95 "⇑" => up

-- Lifting twice pushes renamings inwards
theorem upUp σ x : (⇑ ⇑ σ) x = (var 0 +: var 1 +: (renameVal succ ∘ renameVal succ ∘ σ)) x := by
  cases x; rfl
  case succ n => cases n <;> rfl

-- Lifting var "substitution" does nothing
theorem upId σ (h : ∀ x, σ x = var x) : ∀ x, (⇑ σ) x = var x := by
  intro n; cases n <;> simp [h, up]

-- Lifting respects subsitution extensionality
theorem upExt σ τ (h : ∀ x, σ x = τ x) : ∀ x, (⇑ σ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [h, up]

-- Lifting commutes with composition
theorem upLift ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) : ∀ x, (⇑ σ ∘ lift ξ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [lift, up, ← h]

-- Lifting commutes with succ
theorem upSucc σ : ∀ x, (⇑ σ ∘ succ) x = (renameVal succ ∘ σ) x := by
  intro n; cases n <;> simp [up]

-- Lifting twice commutes with lifted succ
theorem upUpSucc σ : ∀ x, (⇑ ⇑ σ ∘ lift succ) x = (renameVal (lift succ) ∘ ⇑ σ) x := by
  intro n; cases n; simp [lift, up]
  case succ n =>
    calc renameVal succ (renameVal succ (σ n))
      _ = renameVal (succ ∘ succ) (σ n)                       := by rw [renameValComp]
      _ = renameVal ((0 +: succ ∘ succ) ∘ succ) (σ n)         := by rw [renameValExt]; intro n; cases n <;> rfl
      _ = renameVal (0 +: succ ∘ succ) (renameVal succ (σ n)) := by rw [renameValComp]

-- Lifting commutes with injection of renamings into substitutions
theorem upVar ξ : ∀ x, (var ∘ lift ξ) x = (⇑ (var ∘ ξ)) x := by
  intro n; cases n <;> simp [lift, up]

-- Lifting commutes with renaming
theorem upRename ξ σ τ (h : ∀ x, (renameVal ξ ∘ σ) x = τ x) : ∀ x, (renameVal (lift ξ) ∘ ⇑ σ) x = (⇑ τ) x := by
  intro n; cases n; simp [lift, up]
  case succ n => calc
    (renameVal (lift ξ) ∘ renameVal succ) (σ n)
      = renameVal (lift ξ ∘ succ) (σ n)      := by simp [renameValComp]
    _ = (renameVal (succ ∘ ξ)) (σ n)         := by rfl
    _ = (renameVal succ ∘ renameVal ξ) (σ n) := by simp [renameValComp]
    _ = (renameVal succ (renameVal ξ (σ n))) := by rfl
    _ = renameVal succ (τ n)                 := by rw [← h]; rfl

/-*-----------------------
  Applying substitutions
-----------------------*-/

mutual
@[simp]
def substVal (σ : Nat → Val) : Val → Val
  | var s => σ s
  | unit => unit
  | inl v => inl (substVal σ v)
  | inr v => inr (substVal σ v)
  | thunk m => thunk (substCom σ m)

@[simp]
def substCom (σ : Nat → Val) : Com → Com
  | force v => force (substVal σ v)
  | lam m => lam (substCom (⇑ σ) m)
  | app m v => app (substCom σ m) (substVal σ v)
  | ret v => ret (substVal σ v)
  | letin m n => letin (substCom σ m) (substCom (⇑ σ) n)
  | case v m n => case (substVal σ v) (substCom (⇑ σ) m) (substCom (⇑ σ) n)
  | prod m n => prod (substCom σ m) (substCom σ n)
  | fst m => fst (substCom σ m)
  | snd m => snd (substCom σ m)
  | join m n => join (substCom (⇑ σ) m) (substCom σ n)
  | jump j v => jump j (substVal σ v)
end
notation:50 v "⦃" σ "⦄" => substVal σ v
notation:50 m "⦃" σ "⦄" => substCom σ m
notation:50 m "⦃" v "⦄" => substCom (v +: var) m

-- Substitution extensionality
theorem substExt σ τ (h : ∀ x, σ x = τ x) :
  (∀ v, substVal σ v = substVal τ v) ∧
  (∀ m, substCom σ m = substCom τ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upExt]

def substValExt σ τ h := (substExt σ τ h).left
def substComExt σ τ h := (substExt σ τ h).right

-- Applying var "substitution" does nothing
theorem substId σ (h : ∀ x, σ x = var x) :
  (∀ v, substVal σ v = v) ∧
  (∀ m, substCom σ m = m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing σ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upId]

def substValId := (substId var (λ _ ↦ rfl)).left
def substComId := (substId var (λ _ ↦ rfl)).right

-- Substitution/renaming compositionality
theorem substRename ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) :
  (∀ v, substVal σ (renameVal ξ v) = substVal τ v) ∧
  (∀ m, substCom σ (renameCom ξ m) = substCom τ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upLift]

def substRenameVal ξ σ := (substRename ξ σ (σ ∘ ξ) (λ _ ↦ rfl)).left
def substRenameCom ξ σ := (substRename ξ σ (σ ∘ ξ) (λ _ ↦ rfl)).right

-- Renaming/substitution compositionality
theorem renameSubst ξ σ τ (h : ∀ x, (renameVal ξ ∘ σ) x = τ x) :
  (∀ v, renameVal ξ (substVal σ v) = substVal τ v) ∧
  (∀ m, renameCom ξ (substCom σ m) = substCom τ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upRename]

def renameSubstVal ξ σ := (renameSubst ξ σ (renameVal ξ ∘ σ) (λ _ ↦ rfl)).left
def renameSubstCom ξ σ := (renameSubst ξ σ (renameVal ξ ∘ σ) (λ _ ↦ rfl)).right

-- Lifting commutes with substitution
theorem upSubst ρ σ τ (h : ∀ x, (substVal ρ ∘ σ) x = τ x) :
  (∀ x, (substVal (⇑ ρ) ∘ (⇑ σ)) x = (⇑ τ) x) := by
  intro n; cases n; rfl
  case succ n => calc
    (substVal (⇑ ρ) ∘ renameVal succ) (σ n)
    _ = substVal (⇑ ρ ∘ succ) (σ n)         := by rw [← substRenameVal]; rfl
    _ = substVal (renameVal succ ∘ ρ) (σ n) := by rfl
    _ = (renameVal succ ∘ substVal ρ) (σ n) := by rw [← renameSubstVal]; rfl
    _ = renameVal succ (substVal ρ (σ n))   := by rfl
    _ = renameVal succ (τ n)                := by rw [← h]; rfl

-- Substitution compositionality
theorem substComp ρ σ τ (h : ∀ x, (substVal ρ ∘ σ) x = τ x) :
  (∀ v, (substVal ρ ∘ substVal σ) v = substVal τ v) ∧
  (∀ m, (substCom ρ ∘ substCom σ) m = substCom τ m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ρ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upSubst]

def substValComp ρ σ := (substComp ρ σ (substVal ρ ∘ σ) (λ _ ↦ rfl)).left
def substComComp ρ σ := (substComp ρ σ (substVal ρ ∘ σ) (λ _ ↦ rfl)).right

-- Renamings are substitutions
theorem renameToSubst ξ :
  (∀ v, renameVal ξ v = substVal (var ∘ ξ) v) ∧
  (∀ m, renameCom ξ m = substCom (var ∘ ξ) m) := by
  refine ⟨λ v ↦ ?val, λ m ↦ ?com⟩
  mutual_induction v, m generalizing ξ
  all_goals simp <;> try repeat' constructor
  all_goals try rw [← substComExt _ _ (upVar ξ)]
  all_goals apply_rules

def renameToSubstVal ξ := (renameToSubst ξ).left
def renameToSubstCom ξ := (renameToSubst ξ).right

-- Join point renamings commute with substitution
theorem renameJSubst ξ σ m : substCom σ (renameJCom ξ m) = renameJCom ξ (substCom σ m) := by
  mutual_induction m generalizing ξ σ
  all_goals simp; try repeat' constructor
  all_goals apply_rules

/-*-----------------------------------------------------
  Handy dandy derived renaming and substitution lemmas
-----------------------------------------------------*-/

/-* Dropping and combining extended substitutions *-/

theorem substDropVal v w : substVal (v +: var) (renameVal succ w) = w := by
  calc substVal (v +: var) (renameVal succ w)
    _ = substVal var w := by rw [substRenameVal]; rfl
    _ = w := by rw [substValId]

theorem substDropCom v m : substCom (v +: var) (renameCom succ m) = m := by
  calc substCom (v +: var) (renameCom succ m)
    _ = substCom var m := by rw [substRenameCom]; rfl
    _ = m := by rw [substComId]

theorem substDrop₂ σ v₁ v₂ m : substCom (v₁ +: v₂ +: σ) (renameCom (lift succ) m) = substCom (v₁ +: σ) m := by
  calc substCom (v₁ +: v₂ +: σ) (renameCom (lift succ) m)
    _ = substCom ((v₁ +: v₂ +: σ) ∘ lift succ) m   := by rw [substRenameCom]
    _ = substCom (v₁ +: σ) m                       := by rw [substComExt]; intro n; cases n <;> rfl

theorem substUnion σ v m : substCom (v +: var) (substCom (⇑ σ) m) = substCom (v +: σ) m := by
  calc substCom (v +: var) (substCom (⇑ σ) m)
    _ = (substCom (v +: var) ∘ substCom (⇑ σ)) m := rfl
    _ = substCom (substVal (v +: var) ∘ (var 0 +: (renameVal succ ∘ σ))) m :=
      by rw [substComComp]; rfl
    _ = substCom (v +: σ) m :=
      by apply substComExt; intro n; cases n <;> simp; rw [substDropVal]

-- Helper for substUnion
private theorem substUnion₂' σ v₁ v₂ m : substCom (substVal (v₁ +: v₂ +: var) ∘ (⇑ ⇑ σ)) m = substCom (v₁ +: v₂ +: σ) m := by
  apply substComExt
  intro n; cases n; simp [up]
  case succ n =>
    cases n; simp [up]
    case succ n =>
      simp [up]; rw [substRenameVal, substRenameVal]
      have e x : (((v₁+:v₂+:var) ∘ succ) ∘ succ) x = var x := by rfl
      rw [substValExt _ _ e, substValId]

theorem substUnion₂ σ v₁ v₂ m : substCom (v₁ +: v₂ +: var) (substCom (⇑ ⇑ σ) m) = substCom (v₁ +: v₂ +: σ) m := by
  calc substCom (v₁ +: v₂ +: var) (substCom (⇑ ⇑ σ) m)
    _ = (substCom (v₁ +: v₂ +: var) ∘ substCom (⇑ ⇑ σ)) m := rfl
    _ = substCom (substVal (v₁ +: v₂ +: var) ∘ (⇑ ⇑ σ)) m := by rw [substComComp]
    _ = substCom (v₁ +: v₂ +: σ) m := by rw [substUnion₂']

/-* Pushing in lifts and ups through renamings *-/

theorem renameLiftRename ξ m : renameCom (lift ξ) (renameCom succ m) = renameCom succ (renameCom ξ m) := by
  calc renameCom (lift ξ) (renameCom succ m)
    _ = renameCom (lift ξ ∘ succ) m    := by rw [renameComComp]
    _ = renameCom (succ ∘ ξ) m         := by rw [renameComExt]; exact liftSucc ξ
    _ = renameCom succ (renameCom ξ m) := by rw [renameComComp]

theorem renameLiftLiftRename ξ m : renameCom (lift (lift ξ)) (renameCom (lift succ) m) = renameCom (lift succ) (renameCom (lift ξ) m) := by
  calc renameCom (lift (lift ξ)) (renameCom (lift succ) m)
    _ = renameCom (lift (lift ξ) ∘ lift succ) m      := by rw [renameComComp]
    _ = renameCom (lift succ ∘ lift ξ) m             := by rw [renameComExt]; exact liftLiftSucc ξ
    _ = renameCom (lift succ) (renameCom (lift ξ) m) := by rw [renameComComp]

theorem renameUpSubstVal σ v : substVal (⇑ σ) (renameVal succ v) = renameVal succ (substVal σ v) := by
  calc substVal (⇑ σ) (renameVal succ v)
  _ = substVal (⇑ σ ∘ succ) v         := by rw [substRenameVal]
  _ = substVal (renameVal succ ∘ σ) v := by rw [substValExt _ _ (upSucc σ)]
  _ = renameVal succ (substVal σ v)   := by rw [renameSubstVal]

theorem renameUpSubstCom σ m : substCom (⇑ σ) (renameCom succ m) = renameCom succ (substCom σ m) := by
  calc substCom (⇑ σ) (renameCom succ m)
  _ = substCom (⇑ σ ∘ succ) m         := by rw [substRenameCom]
  _ = substCom (renameVal succ ∘ σ) m := by rw [substComExt _ _ (upSucc σ)]
  _ = renameCom succ (substCom σ m)   := by rw [renameSubstCom]

theorem renameUpUpSubst σ m : substCom (⇑ ⇑ σ) (renameCom (lift succ) m) = renameCom (lift succ) (substCom (⇑ σ) m) := by
  calc substCom (⇑ ⇑ σ) (renameCom (lift succ) m)
    _ = substCom (⇑ ⇑ σ ∘ lift succ) m             := by rw [substRenameCom]
    _ = substCom (renameVal (lift succ) ∘ (⇑ σ)) m := by rw [substComExt _ _ (upUpSucc σ)]
    _ = renameCom (lift succ) (substCom (⇑ σ) m)   := by rw [renameSubstCom]

theorem renameUpSubstCons σ v m : substCom (⇑ (v +: σ)) (renameCom (lift succ) m) = substCom (⇑ σ) m := by
  calc substCom (⇑ (v +: σ)) (renameCom (lift succ) m)
    _ = substCom (⇑ (v +: σ) ∘ lift succ) m := by rw [substRenameCom]
    _ = substCom (⇑ σ) m                    := by rw [substComExt]; intro n; cases n <;> rfl

/-* Terrible name but extremely specific lemma for Equivalence.letLet/.letCase I will never use again *-/

theorem renameDropSubst σ m v : ((renameCom (lift succ) m)⦃⇑⇑ σ⦄⦃⇑ (v +: var)⦄) = (m⦃⇑ σ⦄) := by
  calc (renameCom (lift succ) m)⦃⇑⇑ σ⦄⦃⇑ (v +: var)⦄
    _ = (renameCom (lift succ) (m ⦃⇑ σ⦄)⦃⇑ (v +: var)⦄) := by rw [renameUpUpSubst]
    _ = (renameCom (lift succ) (m ⦃⇑ σ⦄)⦃var 0 +: renameVal succ v +: var ∘ succ⦄)
      := by rw [substComExt]; intro n; cases n with | zero => rfl | succ n => cases n <;> rfl
    _ = (m⦃⇑ σ⦄⦃var 0 +: var ∘ succ⦄)                   := by rw [substDrop₂]
    _ = (m⦃⇑ σ⦄⦃var⦄)                                   := by rw [substComExt]; intro n; cases n <;> rfl
    _ = (m⦃⇑ σ⦄)                                        := by rw [substComId]

/-*------------------------
  Contexts and membership
------------------------*-/

inductive Ctxt : Type where
  | nil : Ctxt
  | cons : Ctxt → ValType → Ctxt
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons

inductive In : Nat → ValType → Ctxt → Prop where
  | here {Γ A} : In 0 A (Γ ∷ A)
  | there {Γ x A B} : In x A Γ → In (succ x) A (Γ ∷ B)
notation:40 Γ:41 "∋" x:41 "∶" A:41 => In x A Γ

inductive Dtxt : Type where
  | nil : Dtxt
  | cons : Dtxt → ValType → ComType → Dtxt
notation:50 "⬝" => Dtxt.nil
notation:50 Δ:51 "∷" A:51 "↗" B:51 => Dtxt.cons Δ A B

inductive Jn : Nat → ValType → ComType → Dtxt → Prop where
  | here {Δ A B} : Jn 0 A B (Δ ∷ A ↗ B)
  | there {Δ j A A' B B'} : Jn j A B Δ → Jn (succ j) A B (Δ ∷ A' ↗ B')
notation:40 Δ:41 "∋" j:41 "∶" A:41 "↗" B:41 => Jn j A B Δ

/-*----------------------
  Well-scoped renamings
----------------------*-/

def wRename (ξ : Nat → Nat) (Γ Δ : Ctxt) := ∀ x A, Γ ∋ x ∶ A → Δ ∋ ξ x ∶ A
notation:40 Δ:41 "⊢" ξ:41 "∶" Γ:41 => wRename ξ Γ Δ

theorem wRenameSucc {Γ A} : Γ ∷ A ⊢ succ ∶ Γ := by
  intro x B mem; constructor; assumption

theorem wRenameLift {ξ : Nat → Nat} {Γ Δ A}
  (h : Δ ⊢ ξ ∶ Γ) :
  Δ ∷ A ⊢ lift ξ ∶ Γ ∷ A := by
  intro x B mem
  cases mem with
  | here => exact In.here
  | there => apply_rules [In.there]
