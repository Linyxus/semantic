import Semantic.Consume.Syntax.Ty

namespace Consume

inductive UseMode : Type where
| access : UseMode
| consume : UseMode
| empty : UseMode

inductive Binding : Sig -> Kind -> Type where
| var : Ty .capt s -> Binding s .var
| tvar : PureTy s -> Binding s .tvar
| cvar : UseMode -> CaptureBound s -> Binding s .cvar

def Binding.rename : Binding s1 k -> Rename s1 s2 -> Binding s2 k
| .var T, f => .var (T.rename f)
| .tvar T, f => .tvar (T.rename f)
| .cvar m cb, f => .cvar m (cb.rename f)

inductive Ctx : Sig -> Type where
| empty : Ctx {}
| push : Ctx s -> Binding s k -> Ctx (s,,k)
| lock : Ctx s -> Ctx s

def Ctx.push_var : Ctx s -> Ty .capt s -> Ctx (s,x)
| Γ, T => Γ.push (.var T)

def Ctx.push_tvar : Ctx s -> PureTy s -> Ctx (s,X)
| Γ, T => Γ.push (.tvar T)

def Ctx.push_cvar : Ctx s -> CaptureBound s -> Ctx (s,C)
| Γ, cb => Γ.push (.cvar .access cb)

/-- Push a capture-variable binding at `.consume` use mode (linear capability). -/
def Ctx.push_cvar_consume : Ctx s -> CaptureBound s -> Ctx (s,C)
| Γ, cb => Γ.push (.cvar .consume cb)

infixl:65 ",x:" => Ctx.push_var
infixl:65 ",X<:" => Ctx.push_tvar
infixl:65 ",C<:" => Ctx.push_cvar

/-- A binding is closed if the type it contains is closed. -/
inductive Binding.IsClosed : Binding s k -> Prop where
| var : T.IsClosed -> Binding.IsClosed (.var T)
| tvar : T.IsClosed -> Binding.IsClosed (.tvar T)
| cvar : cb.IsClosed -> Binding.IsClosed (.cvar m cb)

/-- A context is closed if all bindings in it are closed. -/
inductive Ctx.IsClosed : Ctx s -> Prop where
| empty : Ctx.IsClosed .empty
| push : Ctx.IsClosed Γ -> b.IsClosed -> Ctx.IsClosed (.push Γ b)
| lock : Ctx.IsClosed Γ -> Ctx.IsClosed (.lock Γ)

inductive Ctx.LookupTVar : Ctx s -> BVar s .tvar -> PureTy s -> Prop
| here :
  Ctx.LookupTVar (.push Γ (.tvar S)) .here (S.rename Rename.succ)
| there {S : PureTy s} {b : Binding s k} :
  Ctx.LookupTVar Γ X S ->
  Ctx.LookupTVar (.push Γ b) (.there X) (S.rename Rename.succ)
| lock {S : PureTy s} :
  Ctx.LookupTVar Γ X S ->
  Ctx.LookupTVar (.lock Γ) X S

inductive Ctx.LookupVar : Ctx s -> BVar s .var -> Ty .capt s -> Prop
| here :
  Ctx.LookupVar (.push Γ (.var T)) .here (T.rename Rename.succ)
| there {T : Ty .capt s} {b : Binding s k} :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (.push Γ b) (.there x) (T.rename Rename.succ)
| lock {T : Ty .capt s} :
  Ctx.LookupVar Γ x T ->
  Ctx.LookupVar (.lock Γ) x T

/-- Lookup a capture variable in the context. The boolean argument is `true`
iff a lock was encountered on the path to the binding. -/
inductive Ctx.LookupCVar : Ctx s -> BVar s .cvar -> UseMode -> CaptureBound s -> Bool -> Prop
| here :
  Ctx.LookupCVar (.push Γ (.cvar m cb)) .here m (cb.rename Rename.succ) false
| there {b : Binding s k} :
  Ctx.LookupCVar Γ c m cb locked ->
  Ctx.LookupCVar (.push Γ b) (.there c) m (cb.rename Rename.succ) locked
| lock {cb : CaptureBound s} :
  Ctx.LookupCVar Γ c m cb locked ->
  Ctx.LookupCVar (.lock Γ) c m cb true

def Ctx.depth : Ctx s -> Nat
| .empty => 0
| .push Γ _ => Γ.depth + 1
| .lock Γ => Γ.depth + 1

@[simp]
theorem Ctx.depth_lock {Γ : Ctx s} : (Ctx.lock Γ).depth = Γ.depth + 1 := rfl

def Ctx.lookup_tvar : Ctx s -> BVar s .tvar -> PureTy s
| .push _ (.tvar S), .here => S.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_tvar x).rename Rename.succ
| .lock Γ, x => Γ.lookup_tvar x

def Ctx.lookup_var : Ctx s -> BVar s .var -> Ty .capt s
| .push _ (.var T), .here => T.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_var x).rename Rename.succ
| .lock Γ, x => Γ.lookup_var x

/-- Functional lookup for capture variables. The Bool component of the result
is `true` iff a lock was crossed on the way to the binding. -/
def Ctx.lookup_cvar : Ctx s -> BVar s .cvar -> UseMode × CaptureBound s × Bool
| .push _ (.cvar m cb), .here => (m, cb.rename Rename.succ, false)
| .push Γ _, .there c =>
    let p := Γ.lookup_cvar c
    (p.1, p.2.1.rename Rename.succ, p.2.2)
| .lock Γ, c =>
    let p := Γ.lookup_cvar c
    (p.1, p.2.1, true)

/-- Helper for `lookup_tvar'`: structurally recursive on `Ctx s`.
The `rfl` pattern in `.push` cases lets Lean unify the signature equation. -/
def Ctx.lookup_tvar'_aux :
    {s_full : Sig} → (Γ : Ctx s_full) → BVar s_full .tvar → {s' : Sig} → {k_top : Kind} →
    s_full = s' ,, k_top → PureTy s'
| _, .push _ (.tvar S), .here, _, _, rfl => S
| _, .push Γ _, .there x, _, _, rfl => Γ.lookup_tvar x
| _, .lock Γ, x, _, _, h => Γ.lookup_tvar'_aux x h

def Ctx.lookup_tvar' (Γ : Ctx (s,,k)) (x : BVar (s,,k) .tvar) : PureTy s :=
  Ctx.lookup_tvar'_aux Γ x rfl

/-- Helper for `lookup_var'`: structurally recursive on `Ctx s`. -/
def Ctx.lookup_var'_aux :
    {s_full : Sig} → (Γ : Ctx s_full) → BVar s_full .var → {s' : Sig} → {k_top : Kind} →
    s_full = s' ,, k_top → Ty .capt s'
| _, .push _ (.var T), .here, _, _, rfl => T
| _, .push Γ _, .there x, _, _, rfl => Γ.lookup_var x
| _, .lock Γ, x, _, _, h => Γ.lookup_var'_aux x h

def Ctx.lookup_var' (Γ : Ctx (s,,k)) (x : BVar (s,,k) .var) : Ty .capt s :=
  Ctx.lookup_var'_aux Γ x rfl

/-- Helper for `lookup_cvar'`: structurally recursive on `Ctx s`. -/
def Ctx.lookup_cvar'_aux :
    {s_full : Sig} → (Γ : Ctx s_full) → BVar s_full .cvar → {s' : Sig} → {k_top : Kind} →
    s_full = s' ,, k_top → UseMode × CaptureBound s' × Bool
| _, .push _ (.cvar m cb), .here, _, _, rfl => (m, cb, false)
| _, .push Γ _, .there c, _, _, rfl => Γ.lookup_cvar c
| _, .lock Γ, c, _, _, h =>
    let p := Γ.lookup_cvar'_aux c h
    (p.1, p.2.1, true)

def Ctx.lookup_cvar' (Γ : Ctx (s,,k)) (c : BVar (s,,k) .cvar) : UseMode × CaptureBound s × Bool :=
  Ctx.lookup_cvar'_aux Γ c rfl

/-- The functional lookup satisfies the inductive predicate. -/
theorem Ctx.lookup_tvar_spec (Γ : Ctx s) (x : BVar s .tvar) :
    Ctx.LookupTVar Γ x (Γ.lookup_tvar x) := by
  match Γ, x with
  | .push _ (.tvar _), .here => exact LookupTVar.here
  | .push Γ' _, .there x' =>
    simp only [lookup_tvar]
    exact LookupTVar.there (lookup_tvar_spec Γ' x')
  | .lock Γ', x' =>
    simp only [lookup_tvar]
    exact LookupTVar.lock (lookup_tvar_spec Γ' x')

/-- If the inductive predicate holds, the type equals the functional lookup. -/
theorem Ctx.LookupTVar.eq_lookup {Γ : Ctx s} {x : BVar s .tvar} {T : PureTy s}
    (h : Ctx.LookupTVar Γ x T) : T = Γ.lookup_tvar x := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_tvar, ih]
  | lock _ ih => simp only [Ctx.lookup_tvar, ih]

/-- The functional lookup satisfies the inductive predicate. -/
theorem Ctx.lookup_var_spec (Γ : Ctx s) (x : BVar s .var) :
    Ctx.LookupVar Γ x (Γ.lookup_var x) := by
  match Γ, x with
  | .push _ (.var _), .here => exact LookupVar.here
  | .push Γ' _, .there x' =>
    simp only [lookup_var]
    exact LookupVar.there (lookup_var_spec Γ' x')
  | .lock Γ', x' =>
    simp only [lookup_var]
    exact LookupVar.lock (lookup_var_spec Γ' x')

/-- If the inductive predicate holds, the type equals the functional lookup. -/
theorem Ctx.LookupVar.eq_lookup {Γ : Ctx s} {x : BVar s .var} {T : Ty .capt s}
    (h : Ctx.LookupVar Γ x T) : T = Γ.lookup_var x := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_var, ih]
  | lock _ ih => simp only [Ctx.lookup_var, ih]

/-- The functional lookup satisfies the inductive predicate. -/
theorem Ctx.lookup_cvar_spec (Γ : Ctx s) (c : BVar s .cvar) :
    Ctx.LookupCVar Γ c (Γ.lookup_cvar c).1 (Γ.lookup_cvar c).2.1 (Γ.lookup_cvar c).2.2 := by
  match Γ, c with
  | .push _ (.cvar _ _), .here => exact LookupCVar.here
  | .push Γ' b, .there c' =>
    simp only [lookup_cvar]
    exact LookupCVar.there (b := b) (lookup_cvar_spec Γ' c')
  | .lock Γ', c' =>
    simp only [lookup_cvar]
    exact LookupCVar.lock (lookup_cvar_spec Γ' c')

/-- If the inductive predicate holds, the use mode, bound, and lock-flag equal
the functional lookup. -/
theorem Ctx.LookupCVar.eq_lookup {Γ : Ctx s} {c : BVar s .cvar} {m : UseMode}
    {cb : CaptureBound s} {locked : Bool}
    (h : Ctx.LookupCVar Γ c m cb locked) : (m, cb, locked) = Γ.lookup_cvar c := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_cvar, ← ih]
  | lock _ ih => simp only [Ctx.lookup_cvar, ← ih]

/-- The lookup equals the primed lookup renamed by succ. -/
theorem Ctx.lookup_tvar_eq_rename (Γ : Ctx (s,,k)) (x : BVar (s,,k) .tvar) :
    Γ.lookup_tvar x = (Γ.lookup_tvar' x).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases x with
      | here => simp only [lookup_tvar, lookup_tvar', lookup_tvar'_aux]
      | there x' => simp only [lookup_tvar, lookup_tvar', lookup_tvar'_aux]
    | var T => cases x with
      | there x' => simp only [lookup_tvar, lookup_tvar', lookup_tvar'_aux]
    | cvar m cb => cases x with
      | there x' => simp only [lookup_tvar, lookup_tvar', lookup_tvar'_aux]
  | lock Γ' =>
    simp only [lookup_tvar, lookup_tvar', lookup_tvar'_aux]
    exact lookup_tvar_eq_rename Γ' x

/-- The lookup equals the primed lookup renamed by succ. -/
theorem Ctx.lookup_var_eq_rename (Γ : Ctx (s,,k)) (x : BVar (s,,k) .var) :
    Γ.lookup_var x = (Γ.lookup_var' x).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases x with
      | there x' => simp only [lookup_var, lookup_var', lookup_var'_aux]
    | var T => cases x with
      | here => simp only [lookup_var, lookup_var', lookup_var'_aux]
      | there x' => simp only [lookup_var, lookup_var', lookup_var'_aux]
    | cvar m cb => cases x with
      | there x' => simp only [lookup_var, lookup_var', lookup_var'_aux]
  | lock Γ' =>
    simp only [lookup_var, lookup_var', lookup_var'_aux]
    exact lookup_var_eq_rename Γ' x

/-- The lookup equals the primed lookup; the use mode and lock-flag are
preserved and the bound is renamed by succ. -/
theorem Ctx.lookup_cvar_eq (Γ : Ctx (s,,k)) (c : BVar (s,,k) .cvar) :
    Γ.lookup_cvar c =
      ((Γ.lookup_cvar' c).1,
        (Γ.lookup_cvar' c).2.1.rename Rename.succ,
        (Γ.lookup_cvar' c).2.2) := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases c with
      | there c' => simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]
    | var T => cases c with
      | there c' => simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]
    | cvar m cb => cases c with
      | here => simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]
      | there c' => simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]
  | lock Γ' =>
    simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]
    rw [lookup_cvar_eq Γ' c]
    rfl

mutual
/-- Helper: peak up a bound var in context. -/
def CaptureSet.peaksVarBound : (Γ : Ctx s) → (m : Mutability) → BVar s .var → CaptureSet s
| .push Γ (.var T), m, .here =>
    (CaptureSet.peaks Γ T.captureSet).rename Rename.succ |> .applyMut m
| .push Γ _, m, .there x =>
    (peaksVarBound Γ m x).rename Rename.succ
| .lock Γ, m, x => peaksVarBound Γ m x
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
  | .lock Γ, x =>
    rw [CaptureSet.peaksVarBound]
    exact CaptureSet.peaksVarBound_peaksOnly Γ m x
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

/-- Peaks is unaffected by locks at the top of the context. -/
theorem CaptureSet.peaks_lock {Γ : Ctx s} {C : CaptureSet s} :
    CaptureSet.peaks (.lock Γ) C = CaptureSet.peaks Γ C := by
  induction C with
  | empty => simp only [CaptureSet.peaks]
  | union C1 C2 ih1 ih2 =>
    simp only [CaptureSet.peaks]
    rw [ih1, ih2]
  | cvar m c => simp only [CaptureSet.peaks]
  | var m v =>
    cases v with
    | free _ => simp only [CaptureSet.peaks]
    | bound x => simp only [CaptureSet.peaks, CaptureSet.peaksVarBound]

/-- Peakset is unaffected by locks at the top of the context. -/
theorem CaptureSet.peakset_lock {Γ : Ctx s} {C : CaptureSet s} :
    C.peakset (Ctx.lock Γ) = C.peakset Γ := by
  unfold CaptureSet.peakset
  congr 1
  exact peaks_lock

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
            simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks,
              CaptureSet.peaksVarBound]
          | there x' =>
            simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks,
              CaptureSet.peaksVarBound]
        | tvar T =>
          cases x with
          | there x' =>
            simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks,
              CaptureSet.peaksVarBound]
        | cvar cm cb =>
          cases x with
          | there x' =>
            simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks,
              CaptureSet.peaksVarBound]
      | lock Γ' =>
        simp only [CaptureSet.rename, Var.rename, Rename.succ, CaptureSet.peaks,
          CaptureSet.peaksVarBound]

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
    simp only [CaptureSet.applyRO, CaptureSet.peaks] at ih
    rw [ih, CaptureSet.applyRO_rename]
  | .lock Γ', .var m (.bound x) =>
    simp only [CaptureSet.applyRO, CaptureSet.peaks, CaptureSet.peaksVarBound]
    have ih := peaks_applyRO_comm Γ' (.var m (.bound x))
    simp only [CaptureSet.applyRO, CaptureSet.peaks] at ih
    exact ih
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
  | lock _ ih =>
    rw [peaks_lock, peaks_lock]
    exact ih

/-- A peak is accessible if it is bound at `.access` mode (regardless of locks). -/
inductive AccessiblePeak : Ctx s -> BVar s .cvar -> Prop where
| lookup {Γ : Ctx s} :
  Γ.LookupCVar c UseMode.access B locked ->
  -------------------
  AccessiblePeak Γ c

/-- A peak is consumable if it is bound at `.consume` mode and not locked. -/
inductive ConsumablePeak : Ctx s -> BVar s .cvar -> Prop where
| lookup {Γ : Ctx s} :
  Γ.LookupCVar c UseMode.consume B false ->
  -------------------
  ConsumablePeak Γ c

/-- A capture set is accessible if all its peaks are accessible. -/
def CaptureSet.accessible (Γ : Ctx s) (C : CaptureSet s) : Prop :=
  ∀ m c, (CaptureSet.cvar m c) ⊆ C.peaks Γ -> AccessiblePeak Γ c

/-- A capture set is consumable if all its peaks are consumable. -/
def CaptureSet.consumable (Γ : Ctx s) (C : CaptureSet s) : Prop :=
  ∀ m c, (CaptureSet.cvar m c) ⊆ C.peaks Γ -> ConsumablePeak Γ c

end Consume
