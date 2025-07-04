import CBPV.Soundness
import CBPV.NormalAcc

/-*--------------------------------------------
  Inductive normalization of well typed terms
  via soundness of typing wrt semantic typing
--------------------------------------------*-/

theorem normalization' {Γ} :
  (∀ {v : Val} {A}, Γ ⊢ v ∶ A → SNVal v) ∧
  (∀ {m : Com} {B}, Γ ⊢ m ∶ B → SNCom m) := by
  let ⟨soundVal, soundCom⟩ := @soundness Γ
  refine ⟨λ h ↦ ?val, λ h ↦ ?com⟩
  case val =>
    let ⟨_, hA, pv⟩ := soundVal _ _ h _ semCtxtVar
    rw [substValId] at pv
    exact hA.snVal pv
  case com =>
    let ⟨_, hB, pm⟩ := soundCom _ _ h _ semCtxtVar
    rw [substComId] at pm
    exact hB.snCom pm

/-*--------------------------
  Soundness of SNCom/SNVal
  wrt StepVal.SN/StepCom.SN
--------------------------*-/

theorem NeCom.ne {m} (snem : SNeCom m) : NeCom m := by
  mutual_induction snem <;> assumption

theorem SN_soundness :
  (∀ {m}, SNeCom m → StepCom.SN m) ∧
  (∀ {v}, SNVal  v → StepVal.SN v) ∧
  (∀ {m}, SNCom  m → StepCom.SN m) ∧
  (∀ {m n : Com}, m ⤳ n → m ⤳ⁿ n) := by
  refine ⟨λ sne ↦ ?snecom, λ sn ↦ ?snval, λ sn ↦ ?sncom, λ r ↦ ?srcom⟩
  mutual_induction sne, sn, sn, r
  case snecom.force snv => exact .force snv
  case snecom.app snem _ snm snv => exact .app (.ne snem) snm snv
  case snecom.letin snem _ snm snn => exact .letin (.ne snem) snm snn
  case snecom.case snv _ _ snm snn => exact .case snv snm snn
  case snecom.fst snem snm => exact .fst (.ne snem) snm
  case snecom.snd snem snm => exact .snd (.ne snem) snm
  case snval.var => constructor; intro _ r; cases r
  case snval.unit => constructor; intro _ r; cases r
  case snval.inl ih => exact .inl ih
  case snval.inr ih => exact .inr ih
  case snval.thunk ih => exact .thunk ih
  case sncom.lam ih => exact .lam ih
  case sncom.ret ih => exact .ret ih
  case sncom.prod ihm ihn => exact .prod ihm ihn
  case sncom.ne => assumption
  case sncom.red r ih => exact r.closure ih
  all_goals constructor <;> assumption

/-*------------------------------------------
  Well typed terms are strongly normalizing
------------------------------------------*-/

theorem ValWt.normalization {Γ} {v : Val} {A} (h : Γ ⊢ v ∶ A) : StepVal.SN v :=
  SN_soundness.right.left (normalization'.left h)

theorem ComWt.normalization {Γ} {m : Com} {B} (h : Γ ⊢ m ∶ B) : StepCom.SN m :=
  SN_soundness.right.right.left (normalization'.right h)
