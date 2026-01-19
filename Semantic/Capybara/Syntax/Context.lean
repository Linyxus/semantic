import Semantic.Capybara.Syntax.Ty

namespace Capybara

inductive Binding : Sig -> Kind -> Type where
| var : Ty .capt s -> Binding s .var
| tvar : PureTy s -> Binding s .tvar
| cvar : Mutability -> Binding s .cvar

def Binding.rename : Binding s1 k -> Rename s1 s2 -> Binding s2 k
| .var T, f => .var (T.rename f)
| .tvar T, f => .tvar (T.rename f)
| .cvar m, _ => .cvar m

inductive Ctx : Sig -> Type where
| empty : Ctx {}
| push : Ctx s -> Binding s k -> Ctx (s,,k)

def Ctx.push_var : Ctx s -> Ty .capt s -> Ctx (s,x)
| Γ, T => Γ.push (.var T)

def Ctx.push_tvar : Ctx s -> PureTy s -> Ctx (s,X)
| Γ, T => Γ.push (.tvar T)

def Ctx.push_cvar : Ctx s -> Mutability -> Ctx (s,C)
| Γ, m => Γ.push (.cvar m)

infixl:65 ",x:" => Ctx.push_var
infixl:65 ",X<:" => Ctx.push_tvar
infixl:65 ",C<:" => Ctx.push_cvar

/-- A binding is closed if the type it contains is closed. -/
inductive Binding.IsClosed : Binding s k -> Prop where
| var : T.IsClosed -> Binding.IsClosed (.var T)
| tvar : T.IsClosed -> Binding.IsClosed (.tvar T)
| cvar : Binding.IsClosed (.cvar m)

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

inductive Ctx.LookupCVar : Ctx s -> BVar s .cvar -> Mutability -> Prop
| here :
  Ctx.LookupCVar (.push Γ (.cvar m)) .here m
| there {b : Binding s k} :
  Ctx.LookupCVar Γ c m ->
  Ctx.LookupCVar (.push Γ b0) (.there c) m

def Ctx.lookup_tvar : Ctx s -> BVar s .tvar -> PureTy s
| .push _ (.tvar S), .here => S.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_tvar x).rename Rename.succ

def Ctx.lookup_var : Ctx s -> BVar s .var -> Ty .capt s
| .push _ (.var T), .here => T.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_var x).rename Rename.succ

def Ctx.lookup_cvar : Ctx s -> BVar s .cvar -> Mutability
| .push _ (.cvar m), .here => m
| .push Γ _, .there c => Γ.lookup_cvar c

def Ctx.lookup_tvar' : Ctx (s,,k) -> BVar (s,,k) .tvar -> PureTy s
| .push _ (.tvar S), .here => S
| .push Γ _, .there x => Γ.lookup_tvar x

def Ctx.lookup_var' : Ctx (s,,k) -> BVar (s,,k) .var -> Ty .capt s
| .push _ (.var T), .here => T
| .push Γ _, .there x => Γ.lookup_var x

def Ctx.lookup_cvar' : Ctx (s,,k) -> BVar (s,,k) .cvar -> Mutability
| .push _ (.cvar m), .here => m
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

/-- If the inductive predicate holds, the mutability equals the functional lookup. -/
theorem Ctx.LookupCVar.eq_lookup {Γ : Ctx s} {c : BVar s .cvar} {m : Mutability}
    (h : Ctx.LookupCVar Γ c m) : m = Γ.lookup_cvar c := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_cvar, ih]

/-- The lookup equals the primed lookup renamed by succ. -/
theorem Ctx.lookup_tvar_eq_rename (Γ : Ctx (s,,k)) (x : BVar (s,,k) .tvar) :
    Γ.lookup_tvar x = (Γ.lookup_tvar' x).rename Rename.succ := by
  match Γ, x with
  | .push _ (.tvar _), .here => rfl
  | .push _ _, .there _ => simp only [lookup_tvar, lookup_tvar']

/-- The lookup equals the primed lookup renamed by succ. -/
theorem Ctx.lookup_var_eq_rename (Γ : Ctx (s,,k)) (x : BVar (s,,k) .var) :
    Γ.lookup_var x = (Γ.lookup_var' x).rename Rename.succ := by
  match Γ, x with
  | .push _ (.var _), .here => rfl
  | .push _ _, .there _ => simp only [lookup_var, lookup_var']

/-- The lookup equals the primed lookup. -/
theorem Ctx.lookup_cvar_eq (Γ : Ctx (s,,k)) (c : BVar (s,,k) .cvar) :
    Γ.lookup_cvar c = Γ.lookup_cvar' c := by
  match Γ, c with
  | .push _ (.cvar _), .here => rfl
  | .push _ _, .there _ => simp only [lookup_cvar, lookup_cvar']

/-- Recursively expand variable references until reaching capture variables (peaks). -/
def CaptureSet.peaks : Ctx s -> CaptureSet s -> CaptureSet s
| _, .empty => .empty
| Γ, .union cs1 cs2 => (peaks Γ cs1) ∪ (peaks Γ cs2)
| _, .cvar m c => .cvar m c
| _, .var _ (.free x) => {}   -- This is ill-formed, but we just return empty
| .push Γ (.var T), .var m (.bound .here) =>
    (peaks Γ T.captureSet).rename Rename.succ |> .applyMut m
| .push Γ _, .var m (.bound (.there x)) =>
    (peaks Γ (.var m (.bound x))).rename Rename.succ
termination_by Γ cs => (sizeOf Γ, sizeOf cs)

@[simp]
theorem CaptureSet.peaks_union (Γ : Ctx s) (cs1 cs2 : CaptureSet s) :
    CaptureSet.peaks Γ (cs1 ∪ cs2) = CaptureSet.peaks Γ cs1 ∪ CaptureSet.peaks Γ cs2 := by
  conv_lhs => simp only [Union.union]; unfold peaks
  simp only [Union.union]

/-- The peaks function always returns a PeaksOnly capture set. -/
theorem CaptureSet.peaks_peaksOnly (Γ : Ctx s) (cs : CaptureSet s) :
    (peaks Γ cs).PeaksOnly := by
  match Γ, cs with
  | _, .empty =>
    simp only [peaks]
    exact PeaksOnly.empty
  | Γ, .union cs1 cs2 =>
    simp only [peaks]
    exact PeaksOnly.union (peaks_peaksOnly Γ cs1) (peaks_peaksOnly Γ cs2)
  | _, .cvar m c =>
    simp only [peaks]
    exact PeaksOnly.cvar
  | _, .var _ (.free _) =>
    simp only [peaks]
    exact PeaksOnly.empty
  | .push Γ (.var T), .var m (.bound .here) =>
    simp only [peaks]
    exact (peaks_peaksOnly Γ T.captureSet).rename Rename.succ |>.applyMut m
  | .push Γ _, .var m (.bound (.there x)) =>
    simp only [peaks]
    exact (peaks_peaksOnly Γ (.var m (.bound x))).rename Rename.succ
termination_by (sizeOf Γ, sizeOf cs)

def CaptureSet.peakset (Γ : Ctx s) (cs : CaptureSet s) : PeakSet s :=
  ⟨peaks Γ cs, CaptureSet.peaks_peaksOnly Γ cs⟩

theorem CaptureSet.var_peaks {Γ : Ctx s}
  (hb : Γ.LookupVar x T) :
  (CaptureSet.peaks Γ (CaptureSet.var m (.bound x))) = (T.captureSet.applyMut m).peaks Γ := sorry

end Capybara
