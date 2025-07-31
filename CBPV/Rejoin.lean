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

  Join stacks satisfy two important properties:
  * (`rejoinDrop`): Rejoined terminals reduce to those terminals
    with the entire join stack dropped;
  * Rejoining (jump j v) drops j joins (as a de Bruijn index).

  The latter resembles the following:
    J[join 1 = γx. m₁ in ... join j = γx. mⱼ in jump j v]
    ⇒⋆ J[jump 0 v]
  Instead of proving it here,
  it gets combined with the logical relations,
  e.g. `ClosedSemantics.rejoinJump`.

  These definitions are isolated here instead of
  incorporated into Syntax and Evaluation
  because they are not really part of the surface syntax
  or evaluation rules of the language.
---------------------------------------------------------------*-/

@[reducible] def J := List Com

@[simp]
def rejoin (m : Com) : J → Com
  | .nil => m
  | .cons n js => rejoin (join n m) js

@[simp]
def renameJ (ξ : Nat → Nat) : J → J
  | .nil => .nil
  | .cons m js => .cons (renameCom (lift ξ) m) (renameJ ξ js)

@[simp]
def substJ (σ : Nat → Val) : J → J
  | .nil => .nil
  | .cons m js => .cons (m⦃⇑ σ⦄) (substJ σ js)

theorem substRenameJ σ ξ js : substJ σ (renameJ ξ js) = substJ (σ ∘ ξ) js := by
  induction js <;> simp
  case cons ih =>
    refine ⟨?_, ih⟩
    rw [substRenameCom, substComExt _ _ (λ n ↦ ?_)]; cases n <;> simp [up, lift]

theorem renameSubstJ σ ξ js : renameJ ξ (substJ σ js) = substJ (renameVal ξ ∘ σ) js := by
  induction js <;> simp
  case cons ih =>
    refine ⟨?_, ih⟩; rw [renameSubstCom]
    apply substComExt; apply upRename; intros; rfl

theorem substCompJ σ v js : substJ σ (substJ (v +: var) js) = substJ (substVal σ v +: σ) js := by
  induction js <;> simp
  case cons m _ ih => simp [ih, substUpUnion]

theorem substJExt σ τ (h : ∀ x, σ x = τ x) js : substJ σ js = substJ τ js := by
  induction js <;> simp
  case cons ih => exact ⟨substComExt _ _ (upExt σ τ h) _, ih⟩

theorem substJId' σ js (h : ∀ x, σ x = var x) : substJ σ js = js := by
  induction js <;> simp
  case cons ih => rw [(substId (⇑ σ) (upId σ h)).right]; simp [ih]

theorem substJId js : substJ var js = js := substJId' var js (λ _ ↦ rfl)

theorem substJDrop σ v js : substJ (v +: σ) (renameJ succ js) = substJ σ js := by
  rw [substRenameJ]; exact substJExt _ _ (λ _ ↦ rfl) js

theorem substRejoin σ m js : substCom σ (rejoin m js) = rejoin (m⦃σ⦄) (substJ σ js) := by
  induction js generalizing m <;> apply_assumption

theorem Eval.rejoin {m n js} (r : m ⇒ n) : rejoin m js ⇒ rejoin n js := by
  induction js generalizing m n
  case nil => exact r
  case cons ih => simp; exact ih (.join r)

theorem Evals.rejoin {m n js} (r : m ⇒⋆ n) : rejoin m js ⇒⋆ rejoin n js := by
  induction r
  case refl => rfl
  case trans r _ rs => exact .trans (r.rejoin) rs

theorem nf.rejoinDrop {m js} : nf m → rejoin m js ⇒⋆ m := by
  intro nfm; mutual_induction m generalizing nfm js
  all_goals simp at nfm
  case lam | ret | prod =>
    induction js <;> simp [RTC.refl]
    case cons ih =>
      refine .trans' (Evals.rejoin (.once ?_)) ih; constructor

theorem Norm.bwdsRejoin {m n n' js} (r : m ⇒⋆ n) : n ⇓ₙ n' → rejoin m js ⇓ₙ n'
  | ⟨r', nfn⟩ => ⟨.trans' (Evals.rejoin (.trans' r r')) nfn.rejoinDrop, nfn⟩
