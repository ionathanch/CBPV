import CBPV.RTC
import CBPV.Syntax

open ValType ComType Val Com

def SNeVal (v : Val) : Prop := ∃ x, v = var x
def SNeVal.var {x} : SNeVal (var x) := ⟨_, rfl⟩

section
set_option hygiene false
local infix:40 "⤳" => SR
mutual
inductive SNeCom : Com → Prop where
  | force {v} : SNeVal v → SNeCom (force v)
  | app {m v} : SNeCom m → SNVal v → SNeCom (app m v)
  | letin {m n} : SNeCom m → SNCom n → SNeCom (letin m n)
  | case {v m n} : SNeVal v → SNCom m → SNCom n → SNeCom (case v m n)
  | unpair {v m} : SNeVal v → SNCom m → SNeCom (unpair v m)
  | fst {m} : SNeCom m → SNeCom (fst m)
  | snd {m} : SNeCom m → SNeCom (snd m)

inductive SNVal : Val → Prop where
  | var {x} : SNVal (var x)
  | unit : SNVal unit
  | inl {v} : SNVal v → SNVal (inl v)
  | inr {v} : SNVal v → SNVal (inr v)
  | pair {v w} : SNVal v → SNVal w → SNVal (pair v w)
  | thunk {m} : SNCom m → SNVal (thunk m)

inductive SNCom : Com → Prop where
  | lam {m} : SNCom m → SNCom (lam m)
  | ret {v} : SNVal v → SNCom (ret v)
  | prod {m n} : SNCom m → SNCom n → SNCom (prod m n)
  | ne {m} : SNeCom m → SNCom m
  | red {m n : Com} : m ⤳ n → SNCom n → SNCom m

inductive SR : Com → Com → Prop where
  | μ {m} : force (thunk m) ⤳ m
  | β {m : Com} {v} : SNVal v → app (lam m) v ⤳ m⦃v⦄
  | ζ {v m} : SNVal v → letin (ret v) m ⤳ m⦃v⦄
  | ι1 {v m n} : SNVal v → SNCom n → case (inl v) m n ⤳ m⦃v⦄
  | ι2 {v m n} : SNVal v → SNCom m → case (inr v) m n ⤳ n⦃v⦄
  | π {v w m} : SNVal v → SNVal w → unpair (pair v w) m ⤳ m⦃w +: v +: var⦄
  | π1 {m n} : SNCom n → fst (prod m n) ⤳ m
  | π2 {m n} : SNCom m → snd (prod m n) ⤳ n
  | app {m n : Com} {v} : m ⤳ n → app m v ⤳ app n v
  | letin {m m' n : Com} : m ⤳ m' → letin m n ⤳ letin m' n
  | fst {m n} : m ⤳ n → fst m ⤳ fst n
  | snd {m n} : m ⤳ n → snd m ⤳ snd n
end
end
infix:40 "⤳" => SR

@[reducible] def SRs := RTC SR
infix:40 "⤳⋆" => SRs

/-*-----------------------------------------
  Inversion lemmas on strong normalization
-----------------------------------------*-/

theorem SNCom.force_inv {v} (h : SNCom (force v)) : SNVal v := by
  generalize e : force v = m at h
  mutual_induction h generalizing v
  all_goals first | contradiction | subst e
  case ne sne => match sne with
  | .force ⟨_, e⟩ => subst e; exact .var
  case red sn ih r => cases r; exact .thunk sn

/-*-------------------------------
  Congruence on strong reduction
-------------------------------*-/

theorem SRs.app {m n : Com} {v} (r : m ⤳⋆ n) : app m v ⤳⋆ app n v := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.app r₁) r₂

theorem SRs.letin {m m' n : Com} (r : m ⤳⋆ m') : letin m n ⤳⋆ letin m' n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.letin r₁) r₂

theorem SRs.fst {m n : Com} (r : m ⤳⋆ n) : fst m ⤳⋆ fst n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.fst r₁) r₂

theorem SRs.snd {m n : Com} (r : m ⤳⋆ n) : snd m ⤳⋆ snd n := by
  induction r
  case refl => exact .refl
  case trans r₁ _ r₂ => exact .trans (.snd r₁) r₂

theorem SRs.red {m n : Com} (r : m ⤳⋆ n) (h : SNCom n) : SNCom m := by
  induction r
  case refl => assumption
  case trans r _ ih => exact .red r (ih h)

/-*--------------------------------
  Antirenaming and extensionality
--------------------------------*-/

joint {ξ : Nat → Nat}
  theorem SNeCom.antirenaming {m} (snem : SNeCom (renameCom ξ m)) : SNeCom m
  theorem SNVal.antirenaming {v} (snv : SNVal (renameVal ξ v)) : SNVal v
  theorem SNCom.antirenaming {m} (snm : SNCom (renameCom ξ m)) : SNCom m
  theorem SR.antirenaming {m n} (r : renameCom ξ m ⤳ n) : ∃ n', n = renameCom ξ n' ∧ m ⤳ n'
by
  case' SR  => generalize e : renameCom ξ _ = m' at r
  case' SNCom  => generalize e : renameCom ξ _ = m' at snm
  case' SNVal  => generalize e : renameVal ξ _ = v' at snv
  case' SNeCom => generalize e : renameCom ξ _ = m' at snem
  mutual_induction snem, snv, snm, r generalizing ξ
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
  case unpair snev snm ihm =>
    cases m <;> try contradiction
    injection e with ev em
    case unpair v _ =>
    let ⟨_, e⟩ := snev; subst e
    cases v <;> try contradiction
    exact .unpair .var (ihm em)
  case fst ih =>
    cases m <;> try contradiction
    injection e with e
    exact .fst (ih e)
  case snd ih =>
    cases m <;> try contradiction
    injection e with e
    exact .snd (ih e)
  case var ih =>
    cases v <;> try contradiction
    exact .var
  case unit => cases v <;> injection e; constructor
  case inl ih =>
    cases v <;> try contradiction
    injection e with e
    exact .inl (ih e)
  case inr ih =>
    cases v <;> try contradiction
    injection e with e
    exact .inr (ih e)
  case pair ihv ihw =>
    cases v <;> try contradiction
    injection e with ev ew
    exact .pair (ihv ev) (ihw ew)
  case thunk ih =>
    cases v <;> try contradiction
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
  case prod ihm ihn =>
    cases m <;> try contradiction
    injection e with em en
    exact .prod (ihm em) (ihn en)
  case ne ih => exact .ne (ih e)
  case red ihr ihm =>
    let ⟨_, e, r⟩ := ihr e
    exact .red r (ihm (.symm e))
  case μ ih =>
    cases m <;> try contradiction
    injection e with e
    case force v =>
    cases v <;> try contradiction
    injection e with e
    exact ⟨_, .symm e, .μ⟩
  case β ih =>
    cases m <;> try contradiction
    injection e with em ev
    case app m _ =>
    cases m <;> try contradiction
    injection em with em
    subst ev em; rw [renameDist]
    exact ⟨_, rfl, .β (ih rfl)⟩
  case ζ ih =>
    cases m <;> try contradiction
    injection e with ev em
    case letin m _ =>
    cases m <;> try contradiction
    injection ev with ev
    subst ev em; rw [renameDist]
    exact ⟨_, rfl, .ζ (ih rfl)⟩
  case ι1 ihv ihn =>
    cases m <;> try contradiction
    injection e with ev em en
    rename Val => v
    cases v <;> try contradiction
    injection ev with ev
    subst ev em en; rw [renameDist]
    exact ⟨_, rfl, .ι1 (ihv rfl) (ihn rfl)⟩
  case ι2 ihv ihm =>
    cases m <;> try contradiction
    injection e with ev em en
    rename Val => v
    cases v <;> try contradiction
    injection ev with ev
    subst ev em en; rw [renameDist]
    exact ⟨_, rfl, .ι2 (ihv rfl) (ihm rfl)⟩
  case π ihv ihw =>
    cases m <;> try contradiction
    injection e with ev em
    rename Val => v
    cases v <;> try contradiction
    injection ev with ev ew
    subst ev ew em; rw [renameDist₂]
    exact ⟨_, rfl, .π (ihv rfl) (ihw rfl)⟩
  case π1 ihm =>
    cases m <;> try contradiction
    injection e with e
    rename Com => m
    cases m <;> try contradiction
    injection e with em en
    exact ⟨_, .symm em, .π1 (ihm en)⟩
  case π2 ihm =>
    cases m <;> try contradiction
    injection e with e
    rename Com => m
    cases m <;> try contradiction
    injection e with em en
    exact ⟨_, .symm en, .π2 (ihm em)⟩
  case app ihv ihm =>
    cases m <;> try contradiction
    injection e with em ev
    let ⟨_, em, r⟩ := ihm em; subst em ev
    exact ⟨.app _ _, rfl, .app r⟩
  case letin ihm =>
    cases m <;> try contradiction
    injection e with em ev
    let ⟨_, em, r⟩ := ihm em; subst em ev
    exact ⟨.letin _ _, rfl, .letin r⟩
  case fst ihm =>
    cases m <;> try contradiction
    injection e with e
    let ⟨_, e, r⟩ := ihm e; subst e
    exact ⟨.fst _, rfl, .fst r⟩
  case snd ihm =>
    cases m <;> try contradiction
    injection e with e
    let ⟨_, e, r⟩ := ihm e; subst e
    exact ⟨.snd _, rfl, .snd r⟩

theorem extensionality {m x} (h : SNCom (app m (var x))) : SNCom m := by
  generalize e : app m (var x) = m' at h
  mutual_induction h generalizing m x
  all_goals first | contradiction | subst e
  case ne h => cases h with | app snem => exact .ne snem
  case red r =>
    cases r
    case β snm _ =>
      rw [substToRename] at snm
      exact .lam (SNCom.antirenaming snm)
    case app r _ h => exact .red r (h rfl)
