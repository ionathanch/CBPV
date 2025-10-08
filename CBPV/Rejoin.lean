import CBPV.Evaluation

open Nat Val Com

/-*---------------------------------------------------------------
  Join stacks and rejoining

  This is a proof widget used for the logical relations.
  Join stacks resemble just the join frames of CK stacks:
    J ::= □ | J[join j = γx. m in □]

  Rejoining a join stack onto a computation
  is dismantling the stack, or plugging into the innermost hole.
  The final computation must then have the following shape:
    join j₁ = γx. m₁ in ... join jᵢ = γx. mᵢ in m

  These definitions are isolated here instead of
  incorporated into Syntax and Evaluation
  because they are not really part of the surface syntax
  or evaluation rules of the language.
---------------------------------------------------------------*-/

inductive J : Nat → Type where
  | nil : J 0
  | cons {δ} : Com δ → J δ → J (δ + 1)

@[simp]
def Com.rejoin {δ} (m : Com δ) : J δ → Com 0
  | .nil => m
  | .cons n φ => rejoin (join n m) φ

theorem Eval.rejoin {δ m n φ} (r : m ⇒ n) : @rejoin δ m φ ⇒ @rejoin δ n φ := by
  induction φ
  case nil => exact r
  case cons ih => simp; exact ih (.join r)

theorem Eval.rejoin_inv {δ φ m₁ m₂ m} (r : .rejoin (@Com.join δ m₁ m₂) φ ⇒ m) :
  ∃ m', .join m₁ m₂ ⇒ m' ∧ m = .rejoin m' φ := by
  induction φ
  case nil => simpa
  case cons ih =>
    let ⟨_, r, e⟩ := ih r
    cases r with | join r => exact ⟨_, r, e⟩

theorem Evals.rejoin {δ m n φ} (r : m ⇒⋆ n) : @rejoin δ m φ ⇒⋆ @rejoin δ n φ := by
  induction r
  case refl => rfl
  case trans r _ rs => exact .trans (r.rejoin) rs

theorem nf.rejoinDrop {δ m φ} : nf m → rejoin (weakenJCom δ m) φ ⇒⋆ m := by
  intro nfm; cases m
  all_goals simp at nfm
  case lam | ret | prod =>
    induction δ <;> cases φ <;> simp [weakenJCom, RTC.refl]
    case succ ih _ _ =>
      refine .trans' (Evals.rejoin (.once ?_)) ih; constructor

theorem nf.rejoin't {δ m φ} (nfmn't : ¬ @nf δ m) : ¬ nf (rejoin m φ) := by
  induction φ
  case nil => exact nfmn't
  case cons ih => apply ih; simp

theorem Norm.bwdsRejoin {δ m n n' φ} (r : m ⇒⋆ n) : n ⇓ₙ n' → rejoin (weakenJCom δ m) φ ⇓ₙ n'
  | ⟨r', nfn⟩ =>
    ⟨.trans' (Evals.rejoin (Evals.weakenJ (.trans' r r'))) nfn.rejoinDrop, nfn⟩

/-*------------------------------------------------------------------
  Properties of rejoining involving antirenaming:
  * A rejoined computation weakening the first innermost join
    will either reduce under the joins or drop the innermost join.
  * A rejoined computation weakening the second innermost join
    will either reduce under the joins,
    jump to the first join (so the second join can't be discarded),
    or drop both joins (reducing to a terminal).
------------------------------------------------------------------*-/

private theorem Eval.wkJoin {δ} {φ : J δ} {m₁ m₂ m} (r : .rejoin (.join m₁ (renameJCom Fin.succ m₂)) φ ⇒ m) :
  (m = .rejoin m₂ φ) ∨ (∃ m₂', m₂ ⇒ m₂' ∧ m = .rejoin (.join m₁ (renameJCom Fin.succ m₂')) φ) := by
  let ⟨_, r, e⟩ := r.rejoin_inv
  generalize erename : renameJCom Fin.succ m₂ = m₂' at r
  cases r
  case join r =>
    subst erename
    let ⟨n, en, rn⟩ := r.antirenameJ
    subst en; exact .inr ⟨n, rn, e⟩
  all_goals cases m₂ <;> injection erename
  case γ ej _ => cases ej
  case ret | lam | prod => subst_vars; exact .inl rfl
  case join't ej ev => rw [Fin.succ_inj.mp ej]; subst ev; exact .inl e

private theorem Eval.wkJoin₂ {δ} {φ : J δ} {m₁ m₂ m₃ m} (r : .rejoin (.join m₁ (.join m₂ (renameJCom (liftJ .succ) m₃))) φ ⇒ m) :
  (∃ (v : Val), m₃ = .jump 0 v ∧ m = .rejoin (.join m₁ (m₂⦃v⦄)) φ) ∨
  (∃ m₃', m₃ = renameJCom Fin.succ m₃' ∧ m ⇒ .rejoin m₃' φ) ∨
  (∃ m₃', m₃ ⇒ m₃' ∧ m = .rejoin (.join m₁ (.join m₂ (renameJCom (liftJ .succ) m₃'))) φ) := by
  let ⟨_, r, e⟩ := r.rejoin_inv
  generalize erename : renameJCom (liftJ .succ) m₃ = m₃' at r
  cases r with | join r =>
  cases r
  case join r =>
    subst erename
    let ⟨n, en, rn⟩ := r.antirenameJ
    subst en; exact .inr (.inr ⟨n, rn, e⟩)
  all_goals cases m₃ <;> injection erename
  case γ.jump j _ ej ev =>
    match j with
    | ⟨0, lt⟩ => subst ev; exact .inl ⟨_, rfl, e⟩
  case ret | lam | prod =>
    subst_vars; exact .inr (.inl ⟨_, rfl, .rejoin (by constructor)⟩)
  case join't.jump j' v j _ ej ev =>
    match j, j' with
    | ⟨0, _⟩, _ => simp [liftJ] at ej; cases ej
    | ⟨j + 1, lt⟩, ⟨_, _⟩ =>
      simp [liftJ] at ej; subst ej ev
      have ej : Fin.mk (j + 1) lt = Fin.succ (Fin.mk j (lt_of_succ_lt_succ lt)) := by rfl
      rw [ej] at e; subst e
      refine .inr (.inl ⟨jump (Fin.mk j (lt_of_succ_lt_succ lt)) v, rfl, .rejoin .join't⟩)

theorem Norm.wkJoin {δ} {φ : J δ} {m₁ m₂ n} (r : rejoin (.join m₁ (renameJCom Fin.succ m₂)) φ ⇓ₙ n) :
  ∃ m₂', m₂ ⇒⋆ m₂' ∧ rejoin (.join m₁ (renameJCom Fin.succ m₂)) φ ⇒⋆ rejoin m₂' φ ∧ rejoin m₂' φ ⇒⋆ n := by
  cases r with | _ rn nfn =>
  generalize e : rejoin (.join m₁ (renameJCom Fin.succ m₂)) φ = m at rn
  induction rn generalizing m₂
  case refl => subst e; cases nfn.rejoin't (by simp)
  case trans r rs ih =>
    subst e
    match r.wkJoin with
    | .inl e =>
      subst e
      let ⟨_, r, e⟩ := r.rejoin_inv
      refine ⟨_, .refl, ?_, rs⟩; rw [e]
      exact .rejoin (.once r)
    | .inr ⟨n, rn, en⟩ =>
      subst en
      have ⟨_, rn', rjoin, rs⟩ := ih nfn rfl
      refine ⟨_, .trans rn rn', .trans (.rejoin (.join rn.renameJ)) rjoin, rs⟩

theorem Norm.wkJoin₂ {δ} {φ : J δ} {m₁ m₂ m₃ n} (r : rejoin (.join m₁ (.join m₂ (renameJCom (liftJ .succ) m₃))) φ ⇓ₙ n) :
  (∃ (v : Val),
    m₃ ⇒⋆ .jump 0 v ∧
    rejoin (.join m₁ (.join m₂ (renameJCom (liftJ .succ) m₃))) φ ⇒⋆ .rejoin (.join m₁ (m₂⦃v⦄)) φ ∧
    .rejoin (.join m₁ (m₂⦃v⦄)) φ ⇒⋆ n) ∨
  (∃ m₃',
    m₃ ⇒⋆ renameJCom Fin.succ m₃' ∧
    rejoin (.join m₁ (.join m₂ (renameJCom (liftJ .succ) m₃))) φ ⇒⋆ .rejoin m₃' φ ∧
    .rejoin m₃' φ ⇒⋆ n) := by
  cases r with | _ rn nfn =>
  generalize e : rejoin (.join m₁ (.join m₂ (renameJCom (liftJ .succ) m₃))) φ = m at rn
  induction rn generalizing m₃
  case refl => subst e; cases nfn.rejoin't (by simp)
  case trans r rs ih =>
    subst e
    match r.wkJoin₂ with
    | .inl ⟨_, ejump, e⟩ =>
      subst ejump e; exact .inl ⟨_, .refl, .once r, rs⟩
    | .inr (.inl ⟨_, e, r'⟩) =>
      cases rs
      case refl => cases nfn.stepn't r'
      case trans r'' rs =>
        rw [Eval.det r'' r'] at rs; subst e
        let ⟨_, r, e⟩ := r.rejoin_inv; subst e
        refine .inr ⟨_, .refl, .trans r (.once r'), rs⟩
    | .inr (.inr ⟨_, rm₃, e⟩) =>
      subst e
      match ih nfn rfl with
      | .inl ⟨_, rm₃', r', rs⟩ =>
        exact .inl ⟨_, .trans rm₃ rm₃', .trans r r', rs⟩
      | .inr ⟨_, rm₃', r', rs⟩ =>
        exact .inr ⟨_, .trans rm₃ rm₃', .trans r r', rs⟩
