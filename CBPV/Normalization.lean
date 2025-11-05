import CBPV.Soundness
import CBPV.NormalAcc

/-*--------------------------------------------
  Inductive normalization of well typed terms
  via soundness of typing wrt semantic typing
--------------------------------------------*-/

joint {Γ : Ctxt}
  theorem ValWt.normalization' {v : Val} {A} (h : Γ ⊢ v ∶ A) : SNVal v
  theorem ComWt.normalization' {m : Com} {B} (h : Γ ⊢ m ∶ B) : SNCom m
by
  case ValWt =>
    let ⟨_, hA, pv⟩ := soundVal _ _ h _ semCtxtVar
    rw [substValId] at pv
    exact hA.snVal pv
  case ComWt =>
    let ⟨_, hB, pm⟩ := soundCom _ _ h _ semCtxtVar
    rw [substComId] at pm
    exact hB.snCom pm

/-*--------------------------
  Soundness of SNCom/SNVal
  wrt StepVal.SN/StepCom.SN
--------------------------*-/

theorem NeCom.ne {m} (snem : SNeCom m) : NeCom m := by
  mutual_induction snem <;> assumption

joint
  theorem SNeCom.SN_soundness {m} (sne : SNeCom m) : StepCom.SN m
  theorem SNVal.SN_soundness {v} (sn : SNVal v) : StepVal.SN v
  theorem SNCom.SN_soundness {m} (sn : SNCom m) : StepCom.SN m
  theorem SR.SN_soundness {m n : Com} (r : m ⤳ n) : m ⤳ⁿ n
by
  mutual_induction sne, sn, sn, r
  case force snv => exact .force snv
  case app snem _ snm snv => exact .app (.ne snem) snm snv
  case letin snem _ snm snn => exact .letin (.ne snem) snm snn
  case case snv _ _ snm snn => exact .case snv snm snn
  case unpair snev _ snm => exact .unpair snev snm
  case fst snem snm => exact .fst (.ne snem) snm
  case snd snem snm => exact .snd (.ne snem) snm
  case var => constructor; intro _ r; cases r
  case unit => constructor; intro _ r; cases r
  case inl ih => exact .inl ih
  case inr ih => exact .inr ih
  case pair ihv ihw => exact .pair ihv ihw
  case thunk ih => exact .thunk ih
  case lam ih => exact .lam ih
  case ret ih => exact .ret ih
  case prod ihm ihn => exact .prod ihm ihn
  case ne => assumption
  case red r ih => exact r.closure ih
  all_goals constructor <;> assumption

/-*------------------------------------------
  Well typed terms are strongly normalizing
------------------------------------------*-/

theorem ValWt.normalization {Γ} {v : Val} {A} (h : Γ ⊢ v ∶ A) : StepVal.SN v :=
  h.normalization'.SN_soundness

theorem ComWt.normalization {Γ} {m : Com} {B} (h : Γ ⊢ m ∶ B) : StepCom.SN m :=
  h.normalization'.SN_soundness
