import CBPV.CBN

open Nat

/-*-----------------
  Lazy translation
-----------------*-/

/-* Translation of types *-/
section
set_option hygiene false
local notation:40 "⟦" A:41 "⟧ᴸ" => transLazy A
@[simp]
def CBN.SType.transLazy : CBN.SType → ComType
  | .Unit => .F .Unit
  | .Sum A₁ A₂ => .F (.Sum (.U (⟦ A₁ ⟧ᴸ)) (.U (⟦ A₂ ⟧ᴸ)))
  | .Prod B₁ B₂ => .F (.Pair (.U (⟦ B₁ ⟧ᴸ)) (.U (⟦ B₂ ⟧ᴸ)))
  | .Arr A B => .F (.U (.Arr (.U (⟦ A ⟧ᴸ)) (⟦ B ⟧ᴸ)))
end
notation:40 "⟦" A:41 "⟧ᴸ" => CBN.SType.transLazy A

theorem transF (B : CBN.SType) : ∃ A, (⟦ B ⟧ᴸ) = .F A := by
  cases B <;> simp

/-* Translation of contexts *-/
section
set_option hygiene false
local notation:40 "⟦" Γ:41 "⟧ᴸ" => transLazy Γ
@[simp]
def CBN.Ctxt.transLazy : CBN.Ctxt → _root_.Ctxt
  | .nil => .nil
  | .cons Γ A => .cons (⟦ Γ ⟧ᴸ) (.U (⟦ A ⟧ᴸ))
end
notation:40 "⟦" Γ:41 "⟧ᴸ" => CBN.Ctxt.transLazy Γ

/-* Translation of terms *-/
section
set_option hygiene false
local notation:40 "⟦" t:41 "⟧ᴸ" => transLazy t
@[simp]
def CBN.Term.transLazy : CBN.Term → Com
  | .var s => .force (.var s)
  | .unit => .ret .unit
  | .lam t => .ret (.thunk (.lam (⟦ t ⟧ᴸ)))
  | .app t u =>
    .letin (⟦ t ⟧ᴸ)
      (.app (.force (.var 0)) (.thunk (renameCom succ (⟦ u ⟧ᴸ))))
  | .inl t => .ret (.inl (.thunk (⟦ t ⟧ᴸ)))
  | .inr t => .ret (.inr (.thunk (⟦ t ⟧ᴸ)))
  | .case s t u =>
    .letin (⟦ s ⟧ᴸ)
      (.case (.var 0)
        (renameCom (lift succ) (⟦ t ⟧ᴸ))
        (renameCom (lift succ) (⟦ u ⟧ᴸ)))
  | .prod t u => .ret (.pair (.thunk (⟦ t ⟧ᴸ)) (.thunk (⟦ u ⟧ᴸ)))
  | .fst t => .letin (⟦ t ⟧ᴸ) (.unpair (.var 0) (.force (.var 1)))
  | .snd t => .letin (⟦ t ⟧ᴸ) (.unpair (.var 0) (.force (.var 0)))
  | .letin t u =>
    .letin (⟦ t ⟧ᴸ)
      (.letin (.ret (.thunk (.ret (.var 0))))
        (renameCom (lift succ) (⟦ u ⟧ᴸ)))
end
notation:40 "⟦" t:41 "⟧ᴸ" => CBN.Term.transLazy t

/-* Translation of stacks *-/
section
set_option hygiene false
local notation:40 "⟦" k:41 "⟧ᴸ" => transLazy k
@[simp]
def CBN.K.transLazy : CBN.K → CK.K
  | [] => []
  | .app u :: k   => .letin (.app (.force (.var 0))
                        (.thunk (renameCom succ (⟦ u ⟧ᴸ)))) :: (⟦ k ⟧ᴸ)
  | .case t u :: k => .letin (.case (.var 0)
                        (renameCom (lift succ) (⟦ t ⟧ᴸ))
                        (renameCom (lift succ) (⟦ u ⟧ᴸ))) :: (⟦ k ⟧ᴸ)
  | .fst :: k => .letin (.unpair (.var 0) (.force (.var 1))) :: (⟦ k ⟧ᴸ)
  | .snd :: k => .letin (.unpair (.var 0) (.force (.var 0))) :: (⟦ k ⟧ᴸ)
  | .letin u :: k => .letin
                        (.letin (.ret (.thunk (.ret (.var 0))))
                          (renameCom (lift succ) (⟦ u ⟧ᴸ))) :: (⟦ k ⟧ᴸ)
end
notation:40 "⟦" k:41 "⟧ᴸ" => CBN.K.transLazy k

/-* Translation of terms with arbitrary π-expansion *-/
section
set_option hygiene false
local infix:40 "↦ₗ" => expandLazy
inductive CBN.Term.expandLazy : CBN.Term → Com → Prop where
  | var {s} : .var s ↦ₗ .force (.var s)
  | unit : .unit ↦ₗ .ret .unit
  | lam {t m} : t ↦ₗ m → .lam t ↦ₗ .ret (.thunk (.lam m))
  | app {t u m n} : t ↦ₗ m → u ↦ₗ n →
    .app t u ↦ₗ
      .letin m
        (.app (.force (.var 0)) (.thunk (renameCom succ n)))
  | inl {t m} : t ↦ₗ m → .inl t ↦ₗ .ret (.inl (.thunk m))
  | inr {t m} : t ↦ₗ m → .inr t ↦ₗ .ret (.inr (.thunk m))
  | case {s t u ms mt mu} : s ↦ₗ ms → t ↦ₗ mt → u ↦ₗ mu →
    .case s t u ↦ₗ
      .letin ms
        (.case (.var 0)
          (renameCom (lift succ) mt)
          (renameCom (lift succ) mu))
  | prod {t u m n} : t ↦ₗ m → u ↦ₗ n →
    .prod t u ↦ₗ .ret (.pair (.thunk m) (.thunk n))
  | fst {t m} : t ↦ₗ m →
    .fst t ↦ₗ .letin m (.unpair (.var 0) (.force (.var 1)))
  | snd {t m} : t ↦ₗ m →
    .snd t ↦ₗ .letin m (.unpair (.var 0) (.force (.var 0)))
  | letin {t u m n} : t ↦ₗ m → u ↦ₗ n →
    .letin t u ↦ₗ
      .letin m
        (.letin (.ret (.thunk (.ret (.var 0))))
          (renameCom (lift succ) n))
  | ft {t m} : t ↦ₗ m → t ↦ₗ .force (.thunk m)
end
infix:40 "↦ₗ" => CBN.Term.expandLazy

/-*---------------------------------------
  Preservation properties of translation
---------------------------------------*-/

namespace Lazy

theorem transExpand {t} : t ↦ₗ (⟦ t ⟧ᴸ) := by
  induction t <;> constructor <;> assumption

/-* Translation is type preserving *-/

theorem presIn {x A Γ} (h : CBN.In x A Γ) : (⟦ Γ ⟧ᴸ) ∋ x ∶ .U (⟦ A ⟧ᴸ) := by
  induction h <;> constructor; assumption

theorem preservation {Γ t A} (h : Γ ⊢ₛ t ∶ A) : (⟦ Γ ⟧ᴸ) ⊢ (⟦ t ⟧ᴸ) ∶ (⟦ A ⟧ᴸ) := by
  induction h
  case var mem => exact .force (.var (presIn mem))
  case unit => exact .ret .unit
  case lam ih => exact .ret (.thunk (.lam ih))
  case app iht ihu => exact .letin iht (.app (.force (.var .here)) (.thunk (wtWeakenCom ihu)))
  case inl ih => exact .ret (.inl (.thunk ih))
  case inr ih => exact .ret (.inr (.thunk ih))
  case case ihs iht ihu => exact .letin ihs (.case (.var .here) (wtWeakenCom₂ iht) (wtWeakenCom₂ ihu))
  case prod iht ihu => exact .ret (.pair (.thunk iht) (.thunk ihu))
  case fst ih => exact .letin ih (.unpair (.var .here) (.force (.var (.there .here))))
  case snd ih => exact .letin ih (.unpair (.var .here) (.force (.var .here)))
  case letin B₁ _ _ _ iht ihu =>
    let ⟨A, e⟩ := transF B₁
    simp at ihu; rw [e] at iht ihu
    exact .letin iht (.letin (.ret (.thunk (.ret (.var .here)))) (wtWeakenCom₂ ihu))

/-* Translation commutes with renaming and substitution *-/

theorem expandRename {ξ t m} (h : t ↦ₗ m) : CBN.rename ξ t ↦ₗ renameCom ξ m := by
  induction h generalizing ξ
  all_goals try simp [← renameLiftRenameCom, renameLiftLiftRename]
  all_goals constructor <;> apply_assumption

theorem expandUp {σ : Nat → CBN.Term} {σ' : Nat → Val}
  (h : ∀ x, σ x ↦ₗ .force (σ' x)) : ∀ x, (⇑ σ) x ↦ₗ .force ((⇑ σ') x) := by
  have e {ξ v} : .force (renameVal ξ v) = renameCom ξ (.force v) := rfl
  intro n; cases n
  case zero => exact .var
  case succ n => simp [up]; rw [e]; exact expandRename (h n)

theorem expandSubst {σ σ' t} (h : ∀ x, σ x ↦ₗ .force (σ' x)) : CBN.subst σ t ↦ₗ substCom σ' (⟦t⟧ᴸ) := by
  induction t generalizing σ σ'
  all_goals try simp [← renameUpSubstCom, ← renameUpLiftSubst]
  case var => exact h _
  all_goals constructor <;> apply_rules [expandUp]

theorem expandSubstSingle {t u} : CBN.subst (u +: .var) t ↦ₗ (⟦t⟧ᴸ) ⦃ Val.thunk (⟦ u ⟧ᴸ) +: .var ⦄ := by
  refine expandSubst (λ n ↦ ?_); cases n <;> constructor; simp; exact transExpand

theorem simulation {t u k k'} (r : ⟨t, k⟩ ⤳ₙ ⟨u, k'⟩) : ∃ m, ⟨⟦ t ⟧ᴸ, ⟦ k ⟧ᴸ⟩ ⤳⋆ ⟨m, ⟦ k' ⟧ᴸ⟩ ∧ u ↦ₗ m := by
  generalize et : (t, k)  = ck  at r
  generalize eu : (u, k') = ck' at r
  induction r
  all_goals injection et with et ek; subst et ek
  all_goals injection eu with eu ek; subst eu ek
  case β t u =>
    refine ⟨⟦ t ⟧ᴸ ⦃ .thunk (⟦ u ⟧ᴸ) ⦄, ?_, expandSubstSingle⟩
    calc
      _ ⤳ _ := .ζ
      _ ⤳ _ := by exact .app
      _ ⤳ _ := .μ
      _ ⤳ _ := .β
      _ = _ := by simp; rw [← substDropCom]
  case ιl s t _ =>
    refine ⟨⟦ t ⟧ᴸ ⦃ .thunk (⟦ s ⟧ᴸ)⦄, ?_, expandSubstSingle⟩
    calc
      _ ⤳ _ := .ζ
      _ ⤳ _ := by exact .ιl
      _ = _ := by rw [← substUnion, substDropCom₂]
  case ιr s _ u =>
    refine ⟨⟦ u ⟧ᴸ ⦃ .thunk (⟦ s ⟧ᴸ)⦄, ?_, expandSubstSingle⟩
    calc
      _ ⤳ _ := .ζ
      _ ⤳ _ := by exact .ιr
      _ = _ := by rw [← substUnion, substDropCom₂]
  case π1 | π2 =>
    refine ⟨_, ?_, transExpand⟩
    calc
      _ ⤳ _ := .ζ
      _ ⤳ _ := by exact .π
      _ ⤳ _ := by exact .μ
  case ζlam | ζinl | ζinr | ζprod =>
    refine ⟨_, ?_, expandSubstSingle⟩
    calc
      _ ⤳ _ := .ζ
      _ ⤳ _ := by exact .letin
      _ ⤳ _ := .ζ
      _ = _ := by simp [← substUnion, substDropCom₂]
  case app => exact ⟨_, .once .letin, transExpand⟩
  case case => exact ⟨_, .once .letin, transExpand⟩
  case fst => exact ⟨_, .once .letin, transExpand⟩
  case snd => exact ⟨_, .once .letin, transExpand⟩
  case letin! => exact ⟨_, .once .letin, transExpand⟩

end Lazy
