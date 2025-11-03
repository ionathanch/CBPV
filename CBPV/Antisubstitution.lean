import CBPV.NormalInd

open ValType ComType Val Com

/-*-----------------
  Antisubstitution
-----------------*-/

joint {σ : Nat → Val}
  theorem SNeCom.antisubstitution {m} (snem : SNeCom (substCom σ m)) : SNeCom m
  theorem SNVal.antisubstitution {v} (snv : SNVal  (substVal σ v)) : SNVal v
  theorem SNCom.antisubstitution {m} (snm : SNCom  (substCom σ m)) : SNCom m
  theorem SR.antisubstitution {m n} (r : substCom σ m ⤳ n) : (∃ n', n = substCom σ n' ∧ m ⤳ n') ∨ SNeCom m
by
  case' SR     => generalize e : substCom σ _ = m' at r
  case' SNCom  => generalize e : substCom σ _ = m' at snm
  case' SNVal  => generalize e : substVal σ _ = v' at snv
  case' SNeCom => generalize e : substCom σ _ = m' at snem
  mutual_induction snem, snv, snm, r generalizing σ
  case force ih =>
    cases m <;> try contradiction
    injection e with e
    case force v =>
    let ⟨_, e⟩ := ih; subst e
    cases v <;> try contradiction
    exact .force .var
  case app ihm ihv =>
    cases m <;> try contradiction
    injection e with em ev
    exact .app (ihm em) (ihv ev)
  case letin ihm ihn =>
    cases m <;> try contradiction
    injection e with em en
    exact .letin (ihm em) (ihn en)
  case case snev _ ihv ihm ihn =>
    cases m <;> try contradiction
    injection e with ev em en
    case case v _ _ =>
    let ⟨_, e⟩ := snev; subst e
    cases v <;> try contradiction
    exact .case .var (ihm em) (ihn en)
  case var =>
    cases v <;> try contradiction
    exact .var
  case unit =>
    cases v <;> try injection e
    all_goals repeat constructor
  case inl ih =>
    cases v <;> try contradiction
    case var => exact .var
    case inl =>
    injection e with e
    exact .inl (ih e)
  case inr ih =>
    cases v <;> try contradiction
    case var => exact .var
    case inr =>
    injection e with e
    exact .inr (ih e)
  case thunk ih =>
    cases v <;> try contradiction
    case var => exact .var
    case thunk =>
    injection e with e
    exact .thunk (ih e)
  case lam ih =>
    cases m <;> try contradiction
    injection e with e
    exact .lam (ih e)
  case ret ih =>
    cases m <;> try contradiction
    injection e with e
    exact .ret (ih e)
  case ne ih => exact .ne (ih e)
  case red ihr ihm =>
    match ihr e with
    | .inl ⟨_, e, r⟩ =>
      exact .red r (ihm (Eq.symm e))
    | .inr snem => exact .ne snem
  case π ih =>
    cases m <;> try contradiction
    injection e with e
    case force v =>
    cases v <;> try contradiction
    case var => exact .inr (.force .var)
    case thunk =>
    injection e with e
    exact .inl ⟨_, Eq.symm e, .π⟩
  case β ih =>
    cases m <;> try contradiction
    injection e with em ev
    case app m _ =>
    cases m <;> try contradiction
    injection em with em
    subst ev em; rw [substDist]
    exact .inl ⟨_, rfl, .β (ih rfl)⟩
  case ζ ih =>
    cases m <;> try contradiction
    injection e with ev em
    case letin m _ =>
    cases m <;> try contradiction
    injection ev with ev
    subst ev em; rw [substDist]
    exact .inl ⟨_, rfl, .ζ (ih rfl)⟩
  case ι1 ihv ihn =>
    cases m <;> try contradiction
    injection e with ev em en
    case case v _ _ =>
    cases v <;> try contradiction
    case var m n _ => exact .inr (.case .var sorry (ihn en))
    case inl =>
    injection ev with ev
    subst ev em en; rw [substDist]
    exact .inl ⟨_, rfl, .ι1 (ihv rfl) (ihn rfl)⟩
  case ι2 ihv ihm =>
    cases m <;> try contradiction
    injection e with ev em en
    case case v _ _ =>
    cases v <;> try contradiction
    case var m n _ => exact .inr (.case .var (ihm em) sorry)
    case inr =>
    injection ev with ev
    subst ev em en; rw [substDist]
    exact .inl ⟨_, rfl, .ι2 (ihv rfl) (ihm rfl)⟩
  case app ihv ihm =>
    cases m <;> try contradiction
    injection e with em ev
    match ihm em with
    | .inl ⟨_, em, r⟩ =>
      subst em ev
      exact .inl ⟨.app _ _, rfl, .app r⟩
    | .inr snem => exact .inr (.app snem sorry)
  case letin ihn ihm =>
    cases m <;> try contradiction
    injection e with em en
    match ihm em with
    | .inl ⟨_, em, r⟩ =>
      subst em en
      exact .inl ⟨.letin _ _, rfl, .letin r⟩
    | .inr snem => exact .inr (.letin snem sorry)
  all_goals sorry

/-*-----------------------------------------------
  Inversion lemmas depending on antisubstitution
-----------------------------------------------*-/

theorem SNCom.app_inv {m v} (h : SNCom (app m v)) : SNCom m ∧ SNVal v := by
  generalize e : app m v = n at h
  mutual_induction h generalizing m v
  all_goals first | contradiction | subst e
  case ne sne => match sne with
  | .app snem snv => exact ⟨.ne snem, snv⟩
  case red sn ih r =>
    cases r
    case β snv => exact ⟨.lam sn.antisubstitution, snv⟩
    case app r => let ⟨snn, snv⟩ := ih rfl; exact ⟨.red r snn, snv⟩

theorem SNCom.letin_inv {m n} (h : SNCom (letin m n)) : SNCom m ∧ SNCom n := by
  generalize e : letin m n = mn at h
  mutual_induction h generalizing m n
  all_goals first | contradiction | subst e
  case ne sne => match sne with
  | .letin snem snn => exact ⟨.ne snem, snn⟩
  case red sn ih r =>
    cases r
    case ζ snv => exact ⟨.ret snv, sn.antisubstitution⟩
    case letin r => let ⟨snm, snn⟩ := ih rfl; exact ⟨.red r snm, snn⟩
