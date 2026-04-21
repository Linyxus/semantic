import Semantic.Consume.Syntax.Ty

namespace Consume

inductive Binding : Sig -> Kind -> Type where
| var : Ty .capt s -> Binding s .var
| tvar : PureTy s -> Binding s .tvar
| cvar : CaptureBound s -> Binding s .cvar

def Binding.rename : Binding s1 k -> Rename s1 s2 -> Binding s2 k
| .var T, f => .var (T.rename f)
| .tvar T, f => .tvar (T.rename f)
| .cvar cb, f => .cvar (cb.rename f)

inductive Ctx : Sig -> Type where
| empty : Ctx {}
| push : Ctx s -> Binding s k -> Ctx (s,,k)

def Ctx.push_var : Ctx s -> Ty .capt s -> Ctx (s,x)
| Γ, T => Γ.push (.var T)

def Ctx.push_tvar : Ctx s -> PureTy s -> Ctx (s,X)
| Γ, T => Γ.push (.tvar T)

def Ctx.push_cvar : Ctx s -> CaptureBound s -> Ctx (s,C)
| Γ, cb => Γ.push (.cvar cb)

infixl:65 ",x:" => Ctx.push_var
infixl:65 ",X<:" => Ctx.push_tvar
infixl:65 ",C<:" => Ctx.push_cvar

/-- A binding is closed if the type it contains is closed. -/
inductive Binding.IsClosed : Binding s k -> Prop where
| var : T.IsClosed -> Binding.IsClosed (.var T)
| tvar : T.IsClosed -> Binding.IsClosed (.tvar T)
| cvar : cb.IsClosed -> Binding.IsClosed (.cvar cb)

/-- A context is closed if all bindings in it are closed. -/
inductive Ctx.IsClosed : Ctx s -> Prop where
| empty : Ctx.IsClosed .empty
| push : Ctx.IsClosed Γ -> b.IsClosed -> Ctx.IsClosed (.push Γ b)

inductive Ctx.LookupTVar : Ctx s -> BVar s .tvar -> PureTy s -> Prop
| here :
  Ctx.LookupTVar (.push Γ (.tvar S)) .here (S.rename Rename.succ)
| there {S : PureTy s} {b : Binding s k} :
  Ctx.LookupTVar Γ X S ->
  Ctx.LookupTVar (.push Γ b) (.there X) (S.rename Rename.succ)

inductive Ctx.LookupVar : Ctx s -> BVar s .var -> Ty .capt s -> Prop
| here :
  Ctx.LookupVar (.push Γ (.var T)) .here (T.rename Rename.succ)
| there {T : Ty .capt s} {b : Binding s k} :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (.push Γ b) (.there x) (T.rename Rename.succ)

inductive Ctx.LookupCVar : Ctx s -> BVar s .cvar -> CaptureBound s -> Prop
| here :
  Ctx.LookupCVar (.push Γ (.cvar cb)) .here (cb.rename Rename.succ)
| there {b : Binding s k} :
  Ctx.LookupCVar Γ c cb ->
  Ctx.LookupCVar (.push Γ b) (.there c) (cb.rename Rename.succ)

def Ctx.lookup_tvar : Ctx s -> BVar s .tvar -> PureTy s
| .push _ (.tvar S), .here => S.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_tvar x).rename Rename.succ

def Ctx.lookup_var : Ctx s -> BVar s .var -> Ty .capt s
| .push _ (.var T), .here => T.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_var x).rename Rename.succ

def Ctx.lookup_cvar : Ctx s -> BVar s .cvar -> CaptureBound s
| .push _ (.cvar cb), .here => cb.rename Rename.succ
| .push Γ _, .there c => (Γ.lookup_cvar c).rename Rename.succ

def Ctx.lookup_tvar' : Ctx (s,,k) -> BVar (s,,k) .tvar -> PureTy s
| .push _ (.tvar S), .here => S
| .push Γ _, .there x => Γ.lookup_tvar x

def Ctx.lookup_var' : Ctx (s,,k) -> BVar (s,,k) .var -> Ty .capt s
| .push _ (.var T), .here => T
| .push Γ _, .there x => Γ.lookup_var x

def Ctx.lookup_cvar' : Ctx (s,,k) -> BVar (s,,k) .cvar -> CaptureBound s
| .push _ (.cvar cb), .here => cb
| .push Γ _, .there c => Γ.lookup_cvar c

/-- The functional lookup satisfies the inductive predicate. -/
theorem Ctx.lookup_tvar_spec (Γ : Ctx s) (x : BVar s .tvar) :
    Ctx.LookupTVar Γ x (Γ.lookup_tvar x) := by
  match Γ, x with
  | .push _ (.tvar _), .here => exact LookupTVar.here
  | .push Γ' _, .there x' =>
    simp only [lookup_tvar]
    exact LookupTVar.there (lookup_tvar_spec Γ' x')

/-- If the inductive predicate holds, the type equals the functional lookup. -/
theorem Ctx.LookupTVar.eq_lookup {Γ : Ctx s} {x : BVar s .tvar} {T : PureTy s}
    (h : Ctx.LookupTVar Γ x T) : T = Γ.lookup_tvar x := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_tvar, ih]

/-- The functional lookup satisfies the inductive predicate. -/
theorem Ctx.lookup_var_spec (Γ : Ctx s) (x : BVar s .var) :
    Ctx.LookupVar Γ x (Γ.lookup_var x) := by
  match Γ, x with
  | .push _ (.var _), .here => exact LookupVar.here
  | .push Γ' _, .there x' =>
    simp only [lookup_var]
    exact LookupVar.there (lookup_var_spec Γ' x')

/-- If the inductive predicate holds, the type equals the functional lookup. -/
theorem Ctx.LookupVar.eq_lookup {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s}
    (h : Ctx.LookupVar Γ x T) : T = Γ.lookup_var x := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_var, ih]

/-- The functional lookup satisfies the inductive predicate. -/
theorem Ctx.lookup_cvar_spec (Γ : Ctx s) (c : BVar s .cvar) :
    Ctx.LookupCVar Γ c (Γ.lookup_cvar c) := by
  match Γ, c with
  | .push _ (.cvar _), .here => exact LookupCVar.here
  | .push Γ' b, .there c' =>
    simp only [lookup_cvar]
    exact LookupCVar.there (b := b) (lookup_cvar_spec Γ' c')

/-- If the inductive predicate holds, the bound equals the functional lookup. -/
theorem Ctx.LookupCVar.eq_lookup {Γ : Ctx s} {c : BVar s .cvar} {cb : CaptureBound s}
    (h : Ctx.LookupCVar Γ c cb) : cb = Γ.lookup_cvar c := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_cvar, ih]

/-- The lookup equals the primed lookup renamed by succ. -/
theorem Ctx.lookup_tvar_eq_rename (Γ : Ctx (s,,k)) (x : BVar (s,,k) .tvar) :
    Γ.lookup_tvar x = (Γ.lookup_tvar' x).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases x with | here => rfl | there x' => rfl
    | var T => cases x with | there x' => rfl
    | cvar cb => cases x with | there x' => rfl

/-- The lookup equals the primed lookup renamed by succ. -/
theorem Ctx.lookup_var_eq_rename (Γ : Ctx (s,,k)) (x : BVar (s,,k) .var) :
    Γ.lookup_var x = (Γ.lookup_var' x).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases x with | there x' => rfl
    | var T => cases x with | here => rfl | there x' => rfl
    | cvar cb => cases x with | there x' => rfl

/-- The lookup equals the primed lookup renamed by succ. -/
theorem Ctx.lookup_cvar_eq (Γ : Ctx (s,,k)) (c : BVar (s,,k) .cvar) :
    Γ.lookup_cvar c = (Γ.lookup_cvar' c).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases c with | there c' => rfl
    | var T => cases c with | there c' => rfl
    | cvar cb => cases c with | here => rfl | there c' => rfl

mutual
/-- Helper: peak up a bound var in context. -/
def CaptureSet.peaksVarBound : (Γ : Ctx s) → (m : Mutability) → BVar s .var → CaptureSet s
| .push Γ (.var T), m, .here =>
    (CaptureSet.peaks Γ T.captureSet).rename Rename.succ |> .applyMut m
| .push Γ _, m, .there x =>
    (peaksVarBound Γ m x).rename Rename.succ
termination_by Γ _ x => (sizeOf Γ, sizeOf x + 1)

/-- Recursively expand variable references until reaching capture variables (peaks). -/
def CaptureSet.peaks : Ctx s -> CaptureSet s -> CaptureSet s
| _, .empty => .empty
| Γ, .union cs1 cs2 => (peaks Γ cs1) ∪ (peaks Γ cs2)
| _, .cvar m c => .cvar m c
| _, .var _ (.free _) => {}
| Γ, .var m (.bound x) => peaksVarBound Γ m x
termination_by Γ cs => (sizeOf Γ, sizeOf cs)
end


@[simp]
theorem CaptureSet.peaks_union (Γ : Ctx s) (cs1 cs2 : CaptureSet s) :
    CaptureSet.peaks Γ (cs1 ∪ cs2) = CaptureSet.peaks Γ cs1 ∪ CaptureSet.peaks Γ cs2 := by
  conv_lhs => simp only [Union.union]; unfold peaks

mutual
/-- peaksVarBound always returns a PeaksOnly capture set. -/
theorem CaptureSet.peaksVarBound_peaksOnly (Γ : Ctx s) (m : Mutability) (x : BVar s .var) :
    (peaksVarBound Γ m x).PeaksOnly := by
  match Γ, x with
  | .push Γ (.var T), .here =>
    rw [CaptureSet.peaksVarBound]
    exact (CaptureSet.peaks_peaksOnly Γ T.captureSet).rename Rename.succ |>.applyMut m
  | .push Γ _, .there x =>
    rw [CaptureSet.peaksVarBound]
    exact (CaptureSet.peaksVarBound_peaksOnly Γ m x).rename Rename.succ
termination_by (sizeOf Γ, sizeOf x + 1)

/-- The peaks function always returns a PeaksOnly capture set. -/
theorem CaptureSet.peaks_peaksOnly (Γ : Ctx s) (cs : CaptureSet s) :
    (peaks Γ cs).PeaksOnly := by
  match Γ, cs with
  | _, .empty => rw [CaptureSet.peaks]; exact PeaksOnly.empty
  | Γ, .union cs1 cs2 =>
    rw [CaptureSet.peaks]
    exact PeaksOnly.union (CaptureSet.peaks_peaksOnly Γ cs1) (CaptureSet.peaks_peaksOnly Γ cs2)
  | _, .cvar m c => rw [CaptureSet.peaks]; exact PeaksOnly.cvar
  | _, .var _ (.free _) => rw [CaptureSet.peaks]; exact PeaksOnly.empty
  | Γ, .var m (.bound x) =>
    rw [CaptureSet.peaks]
    exact CaptureSet.peaksVarBound_peaksOnly Γ m x
termination_by (sizeOf Γ, sizeOf cs)
end

def CaptureSet.peakset (Γ : Ctx s) (cs : CaptureSet s) : PeakSet s :=
  ⟨peaks Γ cs, CaptureSet.peaks_peaksOnly Γ cs⟩

theorem CaptureSet.peaks_rename_succ_eq {Γ : Ctx s} {b : Binding s k} {C : CaptureSet s} :
  (C.rename Rename.succ).peaks (Γ.push b) = (C.peaks Γ).rename Rename.succ := by
  induction C generalizing k with
  | empty =>
    simp only [CaptureSet.rename, CaptureSet.peaks]
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.rename, CaptureSet.peaks]
    rw [ih1, ih2]
    rfl
  | cvar m c =>
    simp only [CaptureSet.rename, CaptureSet.peaks]
  | var m v =>
    cases v with
    | free _ =>
      simp only [CaptureSet.rename, Var.rename, CaptureSet.peaks]
      rfl
    | bound x =>
      cases Γ with
      | empty => cases x
      | push Γ' bd =>
        cases bd with
        | var T =>
          cases x with
          | here =>
            simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks, CaptureSet.peaksVarBound]
          | there x' =>
            simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks, CaptureSet.peaksVarBound]
        | tvar T =>
          cases x with
          | there x' =>
            simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks, CaptureSet.peaksVarBound]
        | cvar cm =>
          cases x with
          | there x' =>
            simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks, CaptureSet.peaksVarBound]

theorem CaptureSet.peaks_applyRO_comm (Γ : Ctx s) (C : CaptureSet s) :
  C.applyRO.peaks Γ = (C.peaks Γ).applyRO := by
  match Γ, C with
  | _, .empty => simp only [CaptureSet.applyRO, CaptureSet.peaks]
  | Γ, .union C1 C2 =>
    simp only [CaptureSet.applyRO, CaptureSet.peaks]
    rw [peaks_applyRO_comm Γ C1, peaks_applyRO_comm Γ C2]
    rfl
  | _, .cvar _ _ => simp only [CaptureSet.applyRO, CaptureSet.peaks]
  | _, .var _ (.free _) =>
    simp only [CaptureSet.applyRO, CaptureSet.peaks]
    rfl
  | .push Γ' (.var T), .var m (.bound .here) =>
    simp only [CaptureSet.applyRO, CaptureSet.peaks, CaptureSet.peaksVarBound,
      CaptureSet.applyMut_ro, CaptureSet.applyMut_applyRO]
  | .push Γ' _, .var m (.bound (.there x')) =>
    simp only [CaptureSet.applyRO, CaptureSet.peaks, CaptureSet.peaksVarBound]
    have ih := peaks_applyRO_comm Γ' (.var m (.bound x'))
    simp only [CaptureSet.applyRO, CaptureSet.peaks, CaptureSet.peaksVarBound] at ih
    rw [ih, CaptureSet.applyRO_rename]
termination_by (sizeOf Γ, sizeOf C)

theorem CaptureSet.peaks_applyMut_comm {Γ : Ctx s} {C : CaptureSet s} {m : Mutability} :
  (C.applyMut m).peaks Γ = (C.peaks Γ).applyMut m := by
  cases m with
  | epsilon => simp only [CaptureSet.applyMut_epsilon]
  | ro =>
    simp only [CaptureSet.applyMut_ro]
    exact peaks_applyRO_comm Γ C

theorem CaptureSet.var_peaks {Γ : Ctx s}
  (hb : Γ.LookupVar x T) :
  (CaptureSet.peaks Γ (CaptureSet.var m (.bound x))) = (T.captureSet.applyMut m).peaks Γ := by
  induction hb with
  | here =>
    simp only [CaptureSet.peaks, CaptureSet.peaksVarBound, Ty.captureSet_rename,
               peaks_rename_succ_eq, peaks_applyMut_comm]
  | there hb' ih =>
    conv_lhs => unfold peaks peaksVarBound
    simp only [Ty.captureSet_rename]
    rw [show peaks _ (CaptureSet.var m (.bound _)) = peaksVarBound _ m _ from by
          unfold peaks; rfl] at ih
    rw [ih, ← CaptureSet.applyMut_rename, ← peaks_rename_succ_eq]

end Consume
