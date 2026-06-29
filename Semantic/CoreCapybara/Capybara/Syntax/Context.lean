import Semantic.CoreCapybara.Capybara.Syntax.Ty

namespace CoreCapybara

inductive CapyAuthority : Type where
-- This capability may be dropped
| can_drop : CapyAuthority
-- This capability may only be accessed, not dropped
| access_only : CapyAuthority

inductive CapyBinding : Sig -> Kind -> Type where
| var : CapyTy .capt s -> CapyBinding s .var
| tvar : CapyPureTy s -> CapyBinding s .tvar
| cvar : CapyAuthority -> CapyCaptureBound s -> CapyBinding s .cvar

def CapyBinding.rename : CapyBinding s1 k -> Rename s1 s2 -> CapyBinding s2 k
| .var T, f => .var (T.rename f)
| .tvar T, f => .tvar (T.rename f)
| .cvar a cb, f => .cvar a (cb.rename f)

inductive CapyCtx : Sig -> Type where
| empty : CapyCtx {}
| push : CapyCtx s -> CapyBinding s k -> CapyCtx (s,,k)

def CapyCtx.push_var : CapyCtx s -> CapyTy .capt s -> CapyCtx (s,x)
| Γ, T => Γ.push (.var T)

def CapyCtx.push_tvar : CapyCtx s -> CapyPureTy s -> CapyCtx (s,X)
| Γ, T => Γ.push (.tvar T)

def CapyCtx.push_cvar : CapyCtx s -> CapyAuthority -> CapyCaptureBound s -> CapyCtx (s,C)
| Γ, a, cb => Γ.push (.cvar a cb)

def CapyCtx.push_cvar_default : CapyCtx s -> CapyCaptureBound s -> CapyCtx (s,C)
| Γ, cb => Γ.push_cvar .access_only cb

infixl:65 (name := capyPushVar) ",x:" => CapyCtx.push_var
infixl:65 (name := capyPushTVar) ",X<:" => CapyCtx.push_tvar
notation:65 (name := capyPushCVar) Γ:65 ",C[" a:66 "]<:" cb:66 => CapyCtx.push_cvar Γ a cb
infixl:65 (name := capyPushCVarDefault) ",C<:" => CapyCtx.push_cvar_default

/-- A binding is closed if the type it contains is closed. -/
inductive CapyBinding.IsClosed : CapyBinding s k -> Prop where
| var : T.IsClosed -> CapyBinding.IsClosed (.var T)
| tvar : T.IsClosed -> CapyBinding.IsClosed (.tvar T)
| cvar : cb.IsClosed -> CapyBinding.IsClosed (.cvar a cb)

/-- A context is closed if all bindings in it are closed. -/
inductive CapyCtx.IsClosed : CapyCtx s -> Prop where
| empty : CapyCtx.IsClosed .empty
| push : CapyCtx.IsClosed Γ -> b.IsClosed -> CapyCtx.IsClosed (.push Γ b)

inductive CapyCtx.LookupTVar : CapyCtx s -> BVar s .tvar -> CapyPureTy s -> Prop
| here :
  CapyCtx.LookupTVar (.push Γ (.tvar S)) .here (S.rename Rename.succ)
| there {S : CapyPureTy s} {b : CapyBinding s k} :
  CapyCtx.LookupTVar Γ X S ->
  CapyCtx.LookupTVar (.push Γ b) (.there X) (S.rename Rename.succ)

inductive CapyCtx.LookupVar : CapyCtx s -> BVar s .var -> CapyTy .capt s -> Prop
| here :
  CapyCtx.LookupVar (.push Γ (.var T)) .here (T.rename Rename.succ)
| there {T : CapyTy .capt s} {b : CapyBinding s k} :
  CapyCtx.LookupVar Γ x T ->
  CapyCtx.LookupVar (.push Γ b) (.there x) (T.rename Rename.succ)

inductive CapyCtx.LookupCVar :
    CapyCtx s -> BVar s .cvar -> CapyAuthority -> CapyCaptureBound s -> Prop
| here :
  CapyCtx.LookupCVar (.push Γ (.cvar a cb)) .here a (cb.rename Rename.succ)
| there {b : CapyBinding s k} :
  CapyCtx.LookupCVar Γ c a cb ->
  CapyCtx.LookupCVar (.push Γ b) (.there c) a (cb.rename Rename.succ)

def CapyCtx.lookup_tvar : CapyCtx s -> BVar s .tvar -> CapyPureTy s
| .push _ (.tvar S), .here => S.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_tvar x).rename Rename.succ

def CapyCtx.lookup_var : CapyCtx s -> BVar s .var -> CapyTy .capt s
| .push _ (.var T), .here => T.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_var x).rename Rename.succ

def CapyCtx.lookup_cvar : CapyCtx s -> BVar s .cvar -> CapyCaptureBound s
| .push _ (.cvar _ cb), .here => cb.rename Rename.succ
| .push Γ _, .there c => (Γ.lookup_cvar c).rename Rename.succ

def CapyCtx.lookup_authority : CapyCtx s -> BVar s .cvar -> CapyAuthority
| .push _ (.cvar a _), .here => a
| .push Γ _, .there c => Γ.lookup_authority c

/-- Two capture variables are distinct droppable variables in `Γ` when both are
bound with `can_drop` authority and they are not the same de Bruijn variable. -/
def CapyCtx.TwoDistinctDroppable (Γ : CapyCtx s) (c1 c2 : BVar s .cvar) : Prop :=
  Γ.lookup_authority c1 = .can_drop ∧
  Γ.lookup_authority c2 = .can_drop ∧
  c1 ≠ c2

def CapyCtx.lookup_tvar' : CapyCtx (s,,k) -> BVar (s,,k) .tvar -> CapyPureTy s
| .push _ (.tvar S), .here => S
| .push Γ _, .there x => Γ.lookup_tvar x

def CapyCtx.lookup_var' : CapyCtx (s,,k) -> BVar (s,,k) .var -> CapyTy .capt s
| .push _ (.var T), .here => T
| .push Γ _, .there x => Γ.lookup_var x

def CapyCtx.lookup_cvar' : CapyCtx (s,,k) -> BVar (s,,k) .cvar -> CapyCaptureBound s
| .push _ (.cvar _ cb), .here => cb
| .push Γ _, .there c => Γ.lookup_cvar c

/-- The functional lookup satisfies the inductive predicate. -/
theorem CapyCtx.lookup_tvar_spec (Γ : CapyCtx s) (x : BVar s .tvar) :
    CapyCtx.LookupTVar Γ x (Γ.lookup_tvar x) := by
  match Γ, x with
  | .push _ (.tvar _), .here => exact LookupTVar.here
  | .push Γ' _, .there x' =>
    simp only [lookup_tvar]
    exact LookupTVar.there (lookup_tvar_spec Γ' x')

/-- If the inductive predicate holds, the type equals the functional lookup. -/
theorem CapyCtx.LookupTVar.eq_lookup {Γ : CapyCtx s} {x : BVar s .tvar} {T : CapyPureTy s}
    (h : CapyCtx.LookupTVar Γ x T) : T = Γ.lookup_tvar x := by
  induction h with
  | here => rfl
  | there _ ih => simp only [CapyCtx.lookup_tvar, ih]

/-- The functional lookup satisfies the inductive predicate. -/
theorem CapyCtx.lookup_var_spec (Γ : CapyCtx s) (x : BVar s .var) :
    CapyCtx.LookupVar Γ x (Γ.lookup_var x) := by
  match Γ, x with
  | .push _ (.var _), .here => exact LookupVar.here
  | .push Γ' _, .there x' =>
    simp only [lookup_var]
    exact LookupVar.there (lookup_var_spec Γ' x')

/-- If the inductive predicate holds, the type equals the functional lookup. -/
theorem CapyCtx.LookupVar.eq_lookup {Γ : CapyCtx s} {x : BVar s .var} {T : CapyTy .capt s}
    (h : CapyCtx.LookupVar Γ x T) : T = Γ.lookup_var x := by
  induction h with
  | here => rfl
  | there _ ih => simp only [CapyCtx.lookup_var, ih]

/-- The functional lookup satisfies the inductive predicate. -/
theorem CapyCtx.lookup_cvar_spec (Γ : CapyCtx s) (c : BVar s .cvar) :
    CapyCtx.LookupCVar Γ c (Γ.lookup_authority c) (Γ.lookup_cvar c) := by
  match Γ, c with
  | .push _ (.cvar _ _), .here => exact LookupCVar.here
  | .push Γ' b, .there c' =>
    simp only [lookup_cvar, lookup_authority]
    exact LookupCVar.there (b := b) (lookup_cvar_spec Γ' c')

/-- If the inductive predicate holds, the bound equals the functional lookup. -/
theorem CapyCtx.LookupCVar.eq_lookup {Γ : CapyCtx s} {c : BVar s .cvar}
    {a : CapyAuthority} {cb : CapyCaptureBound s}
    (h : CapyCtx.LookupCVar Γ c a cb) : cb = Γ.lookup_cvar c := by
  induction h with
  | here => rfl
  | there _ ih => simp only [CapyCtx.lookup_cvar, ← ih]

/-- If the inductive predicate holds, the authority equals the functional lookup. -/
theorem CapyCtx.LookupCVar.eq_authority {Γ : CapyCtx s} {c : BVar s .cvar}
    {a : CapyAuthority} {cb : CapyCaptureBound s}
    (h : CapyCtx.LookupCVar Γ c a cb) : a = Γ.lookup_authority c := by
  induction h with
  | here => rfl
  | there _ ih => simp only [CapyCtx.lookup_authority, ih]

/-- The lookup equals the primed lookup renamed by succ. -/
theorem CapyCtx.lookup_tvar_eq_rename (Γ : CapyCtx (s,,k)) (x : BVar (s,,k) .tvar) :
    Γ.lookup_tvar x = (Γ.lookup_tvar' x).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases x with | here => rfl | there x' => rfl
    | var T => cases x with | there x' => rfl
    | cvar _ cb => cases x with | there x' => rfl

/-- The lookup equals the primed lookup renamed by succ. -/
theorem CapyCtx.lookup_var_eq_rename (Γ : CapyCtx (s,,k)) (x : BVar (s,,k) .var) :
    Γ.lookup_var x = (Γ.lookup_var' x).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases x with | there x' => rfl
    | var T => cases x with | here => rfl | there x' => rfl
    | cvar _ cb => cases x with | there x' => rfl

/-- The lookup equals the primed lookup renamed by succ. -/
theorem CapyCtx.lookup_cvar_eq (Γ : CapyCtx (s,,k)) (c : BVar (s,,k) .cvar) :
    Γ.lookup_cvar c = (Γ.lookup_cvar' c).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases c with | there c' => rfl
    | var T => cases c with | there c' => rfl
    | cvar _ cb => cases c with | here => rfl | there c' => rfl

mutual
/-- Helper: peak up a bound var in context. -/
def CapyCaptureSet.peaksVarBound : (Γ : CapyCtx s) → (a : Access) → BVar s .var → CapyCaptureSet s
| .push Γ (.var T), m, .here =>
    (CapyCaptureSet.peaks Γ T.captureSet).rename Rename.succ |> .applyAccess m
| .push Γ _, m, .there x =>
    (peaksVarBound Γ m x).rename Rename.succ
termination_by Γ _ x => (sizeOf Γ, sizeOf x + 1)

/-- Recursively expand variable references until reaching capture variables (peaks). -/
def CapyCaptureSet.peaks : CapyCtx s -> CapyCaptureSet s -> CapyCaptureSet s
| _, .empty => .empty
| Γ, .union cs1 cs2 => (peaks Γ cs1) ∪ (peaks Γ cs2)
| _, .cvar m c => .cvar m c
| _, .var _ (.free _) => {}
| Γ, .var m (.bound x) => peaksVarBound Γ m x
termination_by Γ cs => (sizeOf Γ, sizeOf cs)
end

@[simp]
theorem CapyCaptureSet.peaks_union (Γ : CapyCtx s) (cs1 cs2 : CapyCaptureSet s) :
    CapyCaptureSet.peaks Γ (cs1 ∪ cs2)
      = CapyCaptureSet.peaks Γ cs1 ∪ CapyCaptureSet.peaks Γ cs2 := by
  change CapyCaptureSet.peaks Γ (CapyCaptureSet.union cs1 cs2) =
      CapyCaptureSet.peaks Γ cs1 ∪ CapyCaptureSet.peaks Γ cs2
  conv_lhs => unfold CapyCaptureSet.peaks

mutual
/-- peaksVarBound always returns a PeaksOnly capture set. -/
theorem CapyCaptureSet.peaksVarBound_peaksOnly (Γ : CapyCtx s) (m : Access) (x : BVar s .var) :
    (peaksVarBound Γ m x).PeaksOnly := by
  match Γ, x with
  | .push Γ (.var T), .here =>
    rw [CapyCaptureSet.peaksVarBound]
    exact (CapyCaptureSet.peaks_peaksOnly Γ T.captureSet).rename Rename.succ |>.applyAccess m
  | .push Γ _, .there x =>
    rw [CapyCaptureSet.peaksVarBound]
    exact (CapyCaptureSet.peaksVarBound_peaksOnly Γ m x).rename Rename.succ
termination_by (sizeOf Γ, sizeOf x + 1)

/-- The peaks function always returns a PeaksOnly capture set. -/
theorem CapyCaptureSet.peaks_peaksOnly (Γ : CapyCtx s) (cs : CapyCaptureSet s) :
    (peaks Γ cs).PeaksOnly := by
  match Γ, cs with
  | _, .empty => rw [CapyCaptureSet.peaks]; exact CapyCaptureSet.PeaksOnly.empty
  | Γ, .union cs1 cs2 =>
    rw [CapyCaptureSet.peaks]
    exact CapyCaptureSet.PeaksOnly.union
      (CapyCaptureSet.peaks_peaksOnly Γ cs1) (CapyCaptureSet.peaks_peaksOnly Γ cs2)
  | _, .cvar m c => rw [CapyCaptureSet.peaks]; exact CapyCaptureSet.PeaksOnly.cvar
  | _, .var _ (.free _) => rw [CapyCaptureSet.peaks]; exact CapyCaptureSet.PeaksOnly.empty
  | Γ, .var m (.bound x) =>
    rw [CapyCaptureSet.peaks]
    exact CapyCaptureSet.peaksVarBound_peaksOnly Γ m x
termination_by (sizeOf Γ, sizeOf cs)
end

def CapyCaptureSet.peakset (Γ : CapyCtx s) (cs : CapyCaptureSet s) : CapyPeakSet s :=
  ⟨peaks Γ cs, CapyCaptureSet.peaks_peaksOnly Γ cs⟩

/-- The consumed peaks of a capture set in context `Γ`: resolve the capture set
to its peaks, then keep those held at `.drop` access mode. -/
def CapyCaptureSet.consumed_peaks (Γ : CapyCtx s) (cs : CapyCaptureSet s) : CapyCaptureSet s :=
  (CapyCaptureSet.peakset Γ cs).consumed.cs

/-- A peak set is droppable in `Γ` when every capture variable occurring in it
is bound with `can_drop` authority. -/
def CapyPeakSet.droppable (Γ : CapyCtx s) (P : CapyPeakSet s) : Prop :=
  ∀ (a : Access) (c : BVar s .cvar),
    (CapyCaptureSet.cvar a c) ⊆ P.cs → Γ.lookup_authority c = .can_drop

/-- A capture set is droppable in `Γ` when all of its peaks are droppable. -/
def CapyCaptureSet.droppable (Γ : CapyCtx s) (C : CapyCaptureSet s) : Prop :=
  CapyPeakSet.droppable Γ (CapyCaptureSet.peakset Γ C)

/-- A capture set is access-only in `Γ` when none of its peaks is dropped. -/
def CapyCaptureSet.AccessOnly (Γ : CapyCtx s) (C : CapyCaptureSet s) : Prop :=
  ∀ (c : BVar s .cvar), (CapyCaptureSet.cvar .drop c) ⊆ (CapyCaptureSet.peakset Γ C).cs → False

/-- A capture bound is valid in `Γ` when concrete bounds are access-only. -/
def CapyCaptureBound.IsValid (Γ : CapyCtx s) : CapyCaptureBound s -> Prop
| .unbound _ => True
| .bound C => CapyCaptureSet.AccessOnly Γ C

theorem CapyCaptureSet.peaks_rename_succ_eq
    {Γ : CapyCtx s} {b : CapyBinding s k} {C : CapyCaptureSet s} :
  CapyCaptureSet.peaks (Γ.push b) (C.rename Rename.succ)
    = (CapyCaptureSet.peaks Γ C).rename Rename.succ := by
  induction C generalizing k with
  | empty =>
    simp only [CapyCaptureSet.rename, CapyCaptureSet.peaks]
  | union C1 C2 ih1 ih2 =>
    simp only [CapyCaptureSet.rename, CapyCaptureSet.peaks]
    rw [ih1, ih2]
    rfl
  | cvar m c =>
    simp only [CapyCaptureSet.rename, CapyCaptureSet.peaks]
  | var m v =>
    cases v with
    | free _ =>
      simp only [CapyCaptureSet.rename, Var.rename, CapyCaptureSet.peaks]
      rfl
    | bound x =>
      cases Γ with
      | empty => cases x
      | push Γ' bd =>
        cases bd with
        | var T =>
          cases x with
          | here =>
            simp only [
              CapyCaptureSet.rename,
              Var.rename,
              Rename.succ,
              CapyCaptureSet.peaks,
              CapyCaptureSet.peaksVarBound
            ]
          | there x' =>
            simp only [
              CapyCaptureSet.rename,
              Var.rename,
              Rename.succ,
              CapyCaptureSet.peaks,
              CapyCaptureSet.peaksVarBound
            ]
        | tvar T =>
          cases x with
          | there x' =>
            simp only [
              CapyCaptureSet.rename,
              Var.rename,
              Rename.succ,
              CapyCaptureSet.peaks,
              CapyCaptureSet.peaksVarBound
            ]
        | cvar _ cm =>
          cases x with
          | there x' =>
            simp only [
              CapyCaptureSet.rename,
              Var.rename,
              Rename.succ,
              CapyCaptureSet.peaks,
              CapyCaptureSet.peaksVarBound
            ]

theorem CapyCaptureSet.peaks_applyRO_comm (Γ : CapyCtx s) (C : CapyCaptureSet s) :
  CapyCaptureSet.peaks Γ (C.applyRO) = (CapyCaptureSet.peaks Γ C).applyRO := by
  match Γ, C with
  | _, .empty => simp only [CapyCaptureSet.applyRO, CapyCaptureSet.peaks]
  | Γ, .union C1 C2 =>
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.peaks]
    rw [peaks_applyRO_comm Γ C1, peaks_applyRO_comm Γ C2]
    rfl
  | _, .cvar _ _ => simp only [CapyCaptureSet.applyRO, CapyCaptureSet.peaks]
  | _, .var _ (.free _) =>
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.peaks]
    rfl
  | .push Γ' (.var T), .var m (.bound .here) =>
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound,
      CapyCaptureSet.applyAccess_applyRO]
  | .push Γ' _, .var m (.bound (.there x')) =>
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
    have ih := peaks_applyRO_comm Γ' (.var m (.bound x'))
    simp only [CapyCaptureSet.applyRO, CapyCaptureSet.peaks] at ih
    rw [ih, CapyCaptureSet.applyRO_rename]
termination_by (sizeOf Γ, sizeOf C)

theorem CapyCaptureSet.peaks_applyMut_comm {Γ : CapyCtx s} {C : CapyCaptureSet s} {m : Mutability} :
  CapyCaptureSet.peaks Γ (C.applyMut m) = (CapyCaptureSet.peaks Γ C).applyMut m := by
  cases m with
  | epsilon => simp only [CapyCaptureSet.applyMut_epsilon]
  | ro =>
    simp only [CapyCaptureSet.applyMut_ro]
    exact peaks_applyRO_comm Γ C

theorem CapyCaptureSet.peaks_applyDrop_comm (Γ : CapyCtx s) (C : CapyCaptureSet s) :
  CapyCaptureSet.peaks Γ (C.applyDrop) = (CapyCaptureSet.peaks Γ C).applyDrop := by
  match Γ, C with
  | _, .empty => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.peaks]
  | Γ, .union C1 C2 =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.peaks]
    rw [peaks_applyDrop_comm Γ C1, peaks_applyDrop_comm Γ C2]
    rfl
  | _, .cvar _ _ => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.peaks]
  | _, .var _ (.free _) =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.peaks]
    rfl
  | .push Γ' (.var T), .var m (.bound .here) =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound,
      CapyCaptureSet.applyAccess_drop, CapyCaptureSet.applyAccess_applyDrop]
  | .push Γ' _, .var m (.bound (.there x')) =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound]
    have ih := peaks_applyDrop_comm Γ' (.var m (.bound x'))
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.peaks] at ih
    rw [ih, CapyCaptureSet.applyDrop_rename]
termination_by (sizeOf Γ, sizeOf C)

theorem CapyCaptureSet.peaks_applyAccess_comm {Γ : CapyCtx s} {C : CapyCaptureSet s} {a : Access} :
  CapyCaptureSet.peaks Γ (C.applyAccess a) = (CapyCaptureSet.peaks Γ C).applyAccess a := by
  cases a with
  | M m => simp only [CapyCaptureSet.applyAccess_M]; exact peaks_applyMut_comm
  | drop => simp only [CapyCaptureSet.applyAccess_drop]; exact peaks_applyDrop_comm Γ C

theorem CapyCaptureSet.var_peaks {Γ : CapyCtx s}
  (hb : Γ.LookupVar x T) :
  (CapyCaptureSet.peaks Γ (CapyCaptureSet.var m (.bound x)))
    = CapyCaptureSet.peaks Γ (T.captureSet.applyAccess m) := by
  induction hb with
  | here =>
    simp only [CapyCaptureSet.peaks, CapyCaptureSet.peaksVarBound, CapyTy.captureSet_rename,
               peaks_rename_succ_eq, peaks_applyAccess_comm]
  | there hb' ih =>
    conv_lhs => unfold peaks peaksVarBound
    simp only [CapyTy.captureSet_rename]
    rw [show peaks _ (CapyCaptureSet.var m (.bound _)) = peaksVarBound _ m _ from by
          unfold peaks; rfl] at ih
    rw [ih, ← CapyCaptureSet.applyAccess_rename, ← peaks_rename_succ_eq]

/-- Peak-level subsetting -/
def CapyCaptureSet.SubP (Γ : CapyCtx s) (cs1 cs2 : CapyCaptureSet s) : Prop :=
  (CapyCaptureSet.peaks Γ cs1).CoveredBy (CapyCaptureSet.peaks Γ cs2)

/-- Peak-level equivalence -/
def CapyCaptureSet.EquivP (Γ : CapyCtx s) (cs1 cs2 : CapyCaptureSet s) : Prop :=
  CapyCaptureSet.SubP Γ cs1 cs2 ∧ CapyCaptureSet.SubP Γ cs2 cs1

end CoreCapybara
