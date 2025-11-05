import MutualInduction
import Joint

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
  | Pair : ValType → ValType → ValType
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
  | pair : Val → Val → Val
  | thunk : Com → Val

inductive Com : Type where
  | force : Val → Com
  | lam : Com → Com
  | app : Com → Val → Com
  | ret : Val → Com
  | letin : Com → Com → Com
  | case : Val → Com → Com → Com
  | unpair : Val → Com → Com
  | prod : Com → Com → Com
  | fst : Com → Com
  | snd : Com → Com
end
open Val Com

theorem appCong {m m' v v'} : m = m' → v = v' → app m v = app m' v'
  | rfl, rfl => rfl

theorem letinCong {m m' n n'} : m = m' → n = n' → letin m n = letin m' n'
  | rfl, rfl => rfl

theorem prodCong {m m' n n'} : m = m' → n = n' → prod m n = prod m' n'
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
  | pair v w => pair (renameVal ξ v) (renameVal ξ w)
  | thunk m => thunk (renameCom ξ m)

@[simp]
def renameCom (ξ : Nat → Nat) : Com → Com
  | force v => force (renameVal ξ v)
  | lam m => lam (renameCom (lift ξ) m)
  | app m v => app (renameCom ξ m) (renameVal ξ v)
  | ret v => ret (renameVal ξ v)
  | letin m n => letin (renameCom ξ m) (renameCom (lift ξ) n)
  | case v m n => case (renameVal ξ v) (renameCom (lift ξ) m) (renameCom (lift ξ) n)
  | unpair v m => unpair (renameVal ξ v) (renameCom (lift (lift ξ)) m)
  | prod m n => prod (renameCom ξ m) (renameCom ξ n)
  | fst m => fst (renameCom ξ m)
  | snd m => snd (renameCom ξ m)
end

-- Renaming extensionality
joint (ξ ζ : Nat → Nat) (h : ∀ x, ξ x = ζ x)
  theorem renameValExt v : renameVal ξ v = renameVal ζ v
  theorem renameComExt m : renameCom ξ m = renameCom ζ m
by
  mutual_induction v, m generalizing ξ ζ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftExt]

-- Applying identity renaming does nothing
joint
  theorem renameValId v : renameVal id v = v
  theorem renameComId m : renameCom id m = m
by
  mutual_induction v, m
  all_goals simp; try repeat' constructor
  all_goals try assumption
  all_goals try rw [renameComExt (lift id) id]
  all_goals try rw [renameComExt (lift (lift id)) id]
  all_goals apply_rules [liftId]

-- Renamings compose
joint (ξ ζ ς : Nat → Nat) (h : ∀ x, (ξ ∘ ζ) x = ς x)
  private theorem renameValComp' v : (renameVal ξ (renameVal ζ v)) = renameVal ς v
  private theorem renameComComp' m : (renameCom ξ (renameCom ζ m)) = renameCom ς m
by
  mutual_induction v, m generalizing ξ ζ ς
  all_goals simp; try repeat' constructor
  all_goals apply_rules [liftComp]

def renameValComp ξ ζ := renameValComp' ξ ζ (ξ ∘ ζ) (λ _ ↦ rfl)
def renameComComp ξ ζ := renameComComp' ξ ζ (ξ ∘ ζ) (λ _ ↦ rfl)

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

theorem upUpVar ξ : ∀ x, (var ∘ lift (lift ξ)) x = (⇑ ⇑ (var ∘ ξ)) x := by
  intro n; cases n
  case zero => rfl
  case succ n => cases n <;> simp [lift, up]

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
  | pair v w => pair (substVal σ v) (substVal σ w)
  | thunk m => thunk (substCom σ m)

@[simp]
def substCom (σ : Nat → Val) : Com → Com
  | force v => force (substVal σ v)
  | lam m => lam (substCom (⇑ σ) m)
  | app m v => app (substCom σ m) (substVal σ v)
  | ret v => ret (substVal σ v)
  | letin m n => letin (substCom σ m) (substCom (⇑ σ) n)
  | case v m n => case (substVal σ v) (substCom (⇑ σ) m) (substCom (⇑ σ) n)
  | unpair v m => unpair (substVal σ v) (substCom (⇑ ⇑ σ) m)
  | prod m n => prod (substCom σ m) (substCom σ n)
  | fst m => fst (substCom σ m)
  | snd m => snd (substCom σ m)
end
notation:50 v "⦃" σ "⦄" => substVal σ v
notation:50 m "⦃" σ "⦄" => substCom σ m
notation:50 m "⦃" v "⦄" => substCom (v +: var) m

-- Substitution extensionality
joint (σ τ : Nat → Val) (h : ∀ x, σ x = τ x)
  theorem substValExt v : substVal σ v = substVal τ v
  theorem substComExt m : substCom σ m = substCom τ m
by
  mutual_induction v, m generalizing σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upExt]

-- Applying var "substitution" does nothing
joint (σ : Nat → Val) (h : ∀ x, σ x = var x)
  private theorem substValId' v : substVal σ v = v
  private theorem substComId' m : substCom σ m = m
by
  mutual_induction v, m generalizing σ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upId]

def substValId := substValId' var (λ _ ↦ rfl)
def substComId := substComId' var (λ _ ↦ rfl)

-- Substitution/renaming compositionality
joint (ξ : Nat → Nat) (σ τ : Nat → Val) (h : ∀ x, (σ ∘ ξ) x = τ x)
  private theorem substRenameVal' v : substVal σ (renameVal ξ v) = substVal τ v
  private theorem substRenameCom' m : substCom σ (renameCom ξ m) = substCom τ m
by
  mutual_induction v, m generalizing ξ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upLift]

def substRenameVal ξ σ := substRenameVal' ξ σ (σ ∘ ξ) (λ _ ↦ rfl)
def substRenameCom ξ σ := substRenameCom' ξ σ (σ ∘ ξ) (λ _ ↦ rfl)

-- Renaming/substitution compositionality
joint (ξ : Nat → Nat) (σ τ : Nat → Val) (h : ∀ x, (renameVal ξ ∘ σ) x = τ x)
  private theorem renameSubstVal' v : renameVal ξ (substVal σ v) = substVal τ v
  private theorem renameSubstCom' m : renameCom ξ (substCom σ m) = substCom τ m
by
  mutual_induction v, m generalizing ξ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upRename]

def renameSubstVal ξ σ := renameSubstVal' ξ σ (renameVal ξ ∘ σ) (λ _ ↦ rfl)
def renameSubstCom ξ σ := renameSubstCom' ξ σ (renameVal ξ ∘ σ) (λ _ ↦ rfl)

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
joint (ρ σ τ : Nat → Val) (h : ∀ x, (substVal ρ ∘ σ) x = τ x)
  private theorem substValComp' v : (substVal ρ ∘ substVal σ) v = substVal τ v
  private theorem substComComp' m : (substCom ρ ∘ substCom σ) m = substCom τ m
by
  mutual_induction v, m generalizing ρ σ τ
  all_goals simp; try repeat' constructor
  all_goals apply_rules [upSubst]

def substValComp ρ σ := substValComp' ρ σ (substVal ρ ∘ σ) (λ _ ↦ rfl)
def substComComp ρ σ := substComComp' ρ σ (substVal ρ ∘ σ) (λ _ ↦ rfl)

joint (ξ : Nat → Nat)
  theorem renameToSubstVal v : renameVal ξ v = substVal (var ∘ ξ) v
  theorem renameToSubstCom m : renameCom ξ m = substCom (var ∘ ξ) m
by
  mutual_induction v, m generalizing ξ
  all_goals simp <;> try repeat' constructor
  all_goals try rw [← substComExt _ _ (upVar ξ)]
  all_goals try rw [← substComExt _ _ (upUpVar ξ)]
  all_goals apply_rules

/-*-------------------------------------------------
  Handy dandy derived renaming substitution lemmas
-------------------------------------------------*-/

theorem substDropVal v w : w = substVal (v +: var) (renameVal succ w) := by
  calc
    w = substVal var w                         := by rw [substValId]
    _ = substVal (v +: var) (renameVal succ w) := by rw [substRenameVal]; rfl

theorem substDropVal₂ v₁ v₂ w : w = substVal (v₁ +: v₂ +: var) (renameVal succ (renameVal succ w)) := by
  calc
    w = substVal var w := by rw [substValId]
    _ = substVal (v₁ +: v₂ +: var) (renameVal succ (renameVal succ w)) :=
        by rw [renameValComp]; rw [substRenameVal]; rfl

theorem substDropCom v m : m = substCom (v +: var) (renameCom succ m) := by
  calc
    m = substCom var m                         := by rw [substComId]
    _ = substCom (v +: var) (renameCom succ m) := by rw [substRenameCom]; rfl

theorem substDropCom₂ v w m : substCom (v +: w +: .var) (renameCom (lift succ) m) = substCom (v +: var) m := by
  calc substCom (v +: w +: .var) (renameCom (lift succ) m)
    _ = substCom ((v +: w +: var) ∘ lift succ) m := by rw [substRenameCom]
    _ = substCom (v +: var) m                    := by rw [substComExt _ _]; intro n; cases n <;> rfl

theorem substDrop₂ σ v₁ v₂ m : substCom (v₁ +: v₂ +: σ) (renameCom (lift succ) m) = substCom (v₁ +: σ) m := by
  calc substCom (v₁ +: v₂ +: σ) (renameCom (lift succ) m)
    _ = substCom (v₁ +: v₂ +: σ) (substCom (var ∘ lift succ) m)   := by rw [renameToSubstCom]
    _ = (substCom (v₁ +: v₂ +: σ) ∘ substCom (var ∘ lift succ)) m := rfl
    _ = substCom (substVal (v₁ +: v₂ +: σ) ∘ (var ∘ lift succ)) m := by rw [substComComp]
    _ = substCom (v₁ +: σ) m                                      := by rw [substComExt]; intro n; cases n <;> rfl

theorem substUnion σ v m : substCom (v +: σ) m = substCom (v +: var) (substCom (⇑ σ) m) := by
  calc substCom (v +: σ) m
    _ = substCom (substVal (v +: var) ∘ (var 0 +: (renameVal succ ∘ σ))) m :=
        by apply substComExt; intro n; cases n <;> simp; rw [← substDropVal]
    _ = substCom (v +: var) (substCom (⇑ σ) m) :=
        by rw [← substComComp]; rfl

theorem substUnion₂ σ v w m : substCom (v +: w +: σ) m = substCom (v +: w +: var) (substCom (⇑ ⇑ σ) m) := by
  calc substCom (v +: w +: σ) m
    _ = substCom (substVal (v +: w +: var) ∘ ⇑ ⇑ σ) m :=
        by apply substComExt; intro n; cases n <;> simp [up]
           case succ n => cases n <;> simp; rw [← substDropVal₂]
    _ = substCom (v +: w +: var) (substCom (⇑ ⇑ σ) m) :=
        by rw [← substComComp]; rfl

theorem renameDist ξ v m : substCom (renameVal ξ v +: var) (renameCom (lift ξ) m) = renameCom ξ (substCom (v +: var) m) := by
  calc substCom (renameVal ξ v +: var) (renameCom (lift ξ) m)
    _ = substCom ((renameVal ξ v +: var) ∘ lift ξ) m := by rw [substRenameCom]
    _ = substCom (renameVal ξ ∘ (v +: var)) m        := by apply substComExt; intro n; cases n <;> rfl
    _ = renameCom ξ (substCom (v +: var) m)          := by rw [← renameSubstCom]

theorem renameDist₂ ξ v w m : substCom (renameVal ξ v +: renameVal ξ w +: var) (renameCom (lift (lift ξ)) m) = renameCom ξ (substCom (v +: w +: var) m) := by
  calc substCom (renameVal ξ v +: renameVal ξ w +: var) (renameCom (lift (lift ξ)) m)
      = substCom ((renameVal ξ v +: renameVal ξ w +: var) ∘ lift (lift ξ)) m := by rw [substRenameCom]
    _ = substCom (renameVal ξ ∘ (v +: w +: var)) m :=
        by apply substComExt; intro n; cases n; rfl
           case succ n => cases n <;> rfl
    _ = renameCom ξ (substCom (v +: w +: var) m) := by rw [← renameSubstCom]

theorem substDist σ v m : substCom (substVal σ v +: var) (substCom (⇑ σ) m) = substCom σ (substCom (v +: var) m) := by
  calc substCom (substVal σ v +: var) (substCom (⇑ σ) m)
      = substCom (substVal σ v +: σ) m       := by rw [← substUnion]
    _ = substCom (substVal σ ∘ (v +: var)) m := by apply substComExt; intro n; cases n <;> rfl
    _ = (substCom σ ∘ substCom (v +: var)) m := by rw [← substComComp]

theorem substDist₂ σ v w m : substCom (substVal σ v +: substVal σ w +: var) (substCom (⇑ ⇑ σ) m) = substCom σ (substCom (v +: w +: var) m) := by
  calc substCom (substVal σ v +: substVal σ w +: var) (substCom (⇑ ⇑ σ) m)
      = substCom (substVal σ v +: substVal σ w +: σ) m := by rw [← substUnion₂]
    _ = substCom (substVal σ ∘ (v +: w +: var)) m :=
        by apply substComExt; intro n; cases n; rfl
           case succ n => cases n <;> rfl
    _ = (substCom σ ∘ substCom (v +: w +: var)) m := by rw [← substComComp]

theorem substToRename x m : substCom (var x +: var) m = renameCom (x +: id) m := by
  calc substCom (var x +: var) m
    _ = substCom (var ∘ (x +: id)) m := by apply substComExt; intro n; cases n <;> simp
    _ = renameCom (x +: id) m        := by rw [renameToSubstCom]

theorem substToRename₂ x y m : substCom (var x +: var y +: var) m = renameCom (x +: y +: id) m := by
  calc substCom (var x +: var y +: var) m
    _ = substCom (var ∘ (x +: y +: id)) m :=
        by apply substComExt; intro n; cases n; rfl
           case succ n => cases n <;> rfl
    _ = renameCom (x +: y +: id) m := by rw [renameToSubstCom]

theorem substVar σ x m : substCom (var x +: σ) m = renameCom (x +: id) (substCom (⇑ σ) m) := by
  calc substCom (var x +: σ) m
    _ = substCom (var x +: var) (substCom (⇑ σ) m) := substUnion σ (var x) m
    _ = renameCom (x +: id) (substCom (⇑ σ) m)     := substToRename x _

theorem substVar₂ σ x y m : substCom (var x +: var y +: σ) m = renameCom (x +: y +: id) (substCom (⇑ ⇑ σ) m) := by
  calc substCom (var x +: var y +: σ) m
    _ = substCom (var x +: var y +: var) (substCom (⇑ ⇑ σ) m) := substUnion₂ σ (var x) (var y) m
    _ = renameCom (x +: y +: id) (substCom (⇑ ⇑ σ) m)         := substToRename₂ x y _

theorem renameLiftRenameVal ξ v : renameVal succ (renameVal ξ v) = renameVal (lift ξ) (renameVal succ v) := by
  calc renameVal succ (renameVal ξ v)
    _ = renameVal (succ ∘ ξ) v                := by rw [renameValComp]
    _ = renameVal (lift ξ ∘ succ) v           := by rw [renameValExt]; exact liftSucc ξ
    _ = renameVal (lift ξ) (renameVal succ v) := by rw [← renameValComp]

theorem renameLiftRenameCom ξ m : renameCom succ (renameCom ξ m) = renameCom (lift ξ) (renameCom succ m) := by
  calc renameCom succ (renameCom ξ m)
    _ = renameCom (succ ∘ ξ) m                := by rw [renameComComp]
    _ = renameCom (lift ξ ∘ succ) m           := by rw [renameComExt]; exact liftSucc ξ
    _ = renameCom (lift ξ) (renameCom succ m) := by rw [← renameComComp]

theorem renameLiftLiftRename ξ m : renameCom (lift (lift ξ)) (renameCom (lift succ) m) = renameCom (lift succ) (renameCom (lift ξ) m) := by
  calc renameCom (lift (lift ξ)) (renameCom (lift succ) m)
    _ = renameCom (lift (lift ξ) ∘ lift succ) m      := by rw [renameComComp]
    _ = renameCom (lift succ ∘ lift ξ) m             := by rw [renameComExt]; exact liftLiftSucc ξ
    _ = renameCom (lift succ) (renameCom (lift ξ) m) := by rw [← renameComComp]

theorem renameUpSubstVal σ v : renameVal succ (substVal σ v) = substVal (⇑ σ) (renameVal succ v) := by
  calc renameVal succ (substVal σ v)
    _ = substVal (renameVal succ ∘ σ) v   := by rw [renameSubstVal]
    _ = substVal (⇑ σ ∘ succ) v           := by rw [substValExt]; exact upSucc σ
    _ = substVal (⇑ σ) (renameVal succ v) := by rw [substRenameVal]

theorem renameUpSubstCom σ m : renameCom succ (substCom σ m) = substCom (⇑ σ) (renameCom succ m) := by
  calc renameCom succ (substCom σ m)
    _ = substCom (renameVal succ ∘ σ) m   := by rw [renameSubstCom]
    _ = substCom (⇑ σ ∘ succ) m           := by rw [substComExt]; exact upSucc σ
    _ = substCom (⇑ σ) (renameCom succ m) := by rw [substRenameCom]

theorem renameUpLiftSubst σ m : renameCom (lift succ) (substCom (⇑ σ) m) = substCom (⇑ ⇑ σ) (renameCom (lift succ) m) := by
  calc renameCom (lift succ) (substCom (⇑ σ) m)
    _ = substCom (renameVal (lift succ) ∘ (⇑ σ)) m := by rw [renameSubstCom]
    _ = substCom (⇑ ⇑ σ ∘ lift succ) m             := by rw [substComExt]; intro n; rw [upUpSucc σ n]
    _ = substCom (⇑ ⇑ σ) (renameCom (lift succ) m) := by rw [substRenameCom]

-- terrible name but extremely specific lemma for Equivalence.letLet I will never use again
theorem renameDropSubst σ m v : ((renameCom (lift succ) m)⦃⇑⇑ σ⦄⦃⇑ (v +: var)⦄) = (m⦃⇑ σ⦄) := by
  calc (renameCom (lift succ) m)⦃⇑⇑ σ⦄⦃⇑ (v +: var)⦄
    _ = (renameCom (lift succ) (m ⦃⇑ σ⦄)⦃⇑ (v +: var)⦄) := by rw [renameUpLiftSubst]
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

/-*----------------------
  Well-scoped renamings
----------------------*-/

def wRename (ξ : Nat → Nat) Γ Δ := ∀ x A, Γ ∋ x ∶ A → Δ ∋ ξ x ∶ A
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
