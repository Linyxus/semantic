import Semantic.Consume.Syntax.Ty

namespace Consume

/-- A tag on "authority" of a capture variable. -/
inductive Authority : Type where
/-- The variable can be dropped. -/
| can_drop : Authority
/-- The variable can only be accessed, not dropped. -/
| access_only : Authority

inductive Binding : Sig -> Kind -> Type where
| var : Ty .capt s -> Binding s .var
| tvar : PureTy s -> Binding s .tvar
| cvar : Authority -> CaptureBound s -> Binding s .cvar

def Binding.rename : Binding s1 k -> Rename s1 s2 -> Binding s2 k
| .var T, f => .var (T.rename f)
| .tvar T, f => .tvar (T.rename f)
| .cvar a cb, f => .cvar a (cb.rename f)

inductive Ctx : Sig -> Type where
| empty : Ctx {}
| push : Ctx s -> Binding s k -> Ctx (s,,k)

def Ctx.push_var : Ctx s -> Ty .capt s -> Ctx (s,x)
| Γ, T => Γ.push (.var T)

def Ctx.push_tvar : Ctx s -> PureTy s -> Ctx (s,X)
| Γ, T => Γ.push (.tvar T)

def Ctx.push_cvar : Ctx s -> Authority -> CaptureBound s -> Ctx (s,C)
| Γ, a, cb => Γ.push (.cvar a cb)

infixl:65 ",x:" => Ctx.push_var
infixl:65 ",X<:" => Ctx.push_tvar
notation:65 Γ:65 ",C[" a:66 "]<:" cb:66 => Ctx.push_cvar Γ a cb

/-- A binding is closed if the type it contains is closed. -/
inductive Binding.IsClosed : Binding s k -> Prop where
| var : T.IsClosed -> Binding.IsClosed (.var T)
| tvar : T.IsClosed -> Binding.IsClosed (.tvar T)
| cvar : cb.IsClosed -> Binding.IsClosed (.cvar a cb)

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

/-- Lookup a capture variable in the context, returning both its `Authority`
and its capture bound. The authority carries no signature dependence, so it is
unaffected by the `succ`-renaming applied to the bound. -/
inductive Ctx.LookupCVar : Ctx s -> BVar s .cvar -> Authority -> CaptureBound s -> Prop
| here :
  Ctx.LookupCVar (.push Γ (.cvar a cb)) .here a (cb.rename Rename.succ)
| there {b : Binding s k} :
  Ctx.LookupCVar Γ c a cb ->
  Ctx.LookupCVar (.push Γ b) (.there c) a (cb.rename Rename.succ)

def Ctx.depth : Ctx s -> Nat
| .empty => 0
| .push Γ _ => Γ.depth + 1

-- RETIRED (2026-05-25): `lock` removed from `Ctx`.
-- @[simp]
-- theorem Ctx.depth_lock {Γ : Ctx s} : (Ctx.lock Γ).depth = Γ.depth + 1 := rfl

def Ctx.lookup_tvar : Ctx s -> BVar s .tvar -> PureTy s
| .push _ (.tvar S), .here => S.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_tvar x).rename Rename.succ

def Ctx.lookup_var : Ctx s -> BVar s .var -> Ty .capt s
| .push _ (.var T), .here => T.rename Rename.succ
| .push Γ _, .there x => (Γ.lookup_var x).rename Rename.succ

/-- Functional lookup for capture variables. -/
def Ctx.lookup_cvar : Ctx s -> BVar s .cvar -> CaptureBound s
| .push _ (.cvar _ cb), .here => cb.rename Rename.succ
| .push Γ _, .there c => (Γ.lookup_cvar c).rename Rename.succ

/-- Functional lookup for the authority of a capture variable. The authority is
a plain tag with no signature dependence, so no renaming is needed. -/
def Ctx.lookup_authority : Ctx s -> BVar s .cvar -> Authority
| .push _ (.cvar a _), .here => a
| .push Γ _, .there c => Γ.lookup_authority c

/-- Helper for `lookup_tvar'`: structurally recursive on `Ctx s`.
The `rfl` pattern in `.push` cases lets Lean unify the signature equation. -/
def Ctx.lookup_tvar'_aux :
    {s_full : Sig} → (Γ : Ctx s_full) → BVar s_full .tvar → {s' : Sig} → {k_top : Kind} →
    s_full = s' ,, k_top → PureTy s'
| _, .push _ (.tvar S), .here, _, _, rfl => S
| _, .push Γ _, .there x, _, _, rfl => Γ.lookup_tvar x

def Ctx.lookup_tvar' (Γ : Ctx (s,,k)) (x : BVar (s,,k) .tvar) : PureTy s :=
  Ctx.lookup_tvar'_aux Γ x rfl

/-- Helper for `lookup_var'`: structurally recursive on `Ctx s`. -/
def Ctx.lookup_var'_aux :
    {s_full : Sig} → (Γ : Ctx s_full) → BVar s_full .var → {s' : Sig} → {k_top : Kind} →
    s_full = s' ,, k_top → Ty .capt s'
| _, .push _ (.var T), .here, _, _, rfl => T
| _, .push Γ _, .there x, _, _, rfl => Γ.lookup_var x

def Ctx.lookup_var' (Γ : Ctx (s,,k)) (x : BVar (s,,k) .var) : Ty .capt s :=
  Ctx.lookup_var'_aux Γ x rfl

/-- Helper for `lookup_cvar'`: structurally recursive on `Ctx s`. -/
def Ctx.lookup_cvar'_aux :
    {s_full : Sig} → (Γ : Ctx s_full) → BVar s_full .cvar → {s' : Sig} → {k_top : Kind} →
    s_full = s' ,, k_top → CaptureBound s'
| _, .push _ (.cvar _ cb), .here, _, _, rfl => cb
| _, .push Γ _, .there c, _, _, rfl => Γ.lookup_cvar c

def Ctx.lookup_cvar' (Γ : Ctx (s,,k)) (c : BVar (s,,k) .cvar) : CaptureBound s :=
  Ctx.lookup_cvar'_aux Γ c rfl

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

/-- The functional lookups (authority and bound) jointly satisfy the inductive
predicate. -/
theorem Ctx.lookup_cvar_spec (Γ : Ctx s) (c : BVar s .cvar) :
    Ctx.LookupCVar Γ c (Γ.lookup_authority c) (Γ.lookup_cvar c) := by
  match Γ, c with
  | .push _ (.cvar _ _), .here => exact LookupCVar.here
  | .push Γ' b, .there c' =>
    simp only [lookup_cvar, lookup_authority]
    exact LookupCVar.there (b := b) (lookup_cvar_spec Γ' c')

/-- If the inductive predicate holds, the bound equals the functional lookup. -/
theorem Ctx.LookupCVar.eq_lookup {Γ : Ctx s} {c : BVar s .cvar}
    {a : Authority} {cb : CaptureBound s}
    (h : Ctx.LookupCVar Γ c a cb) : cb = Γ.lookup_cvar c := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_cvar, ← ih]

/-- If the inductive predicate holds, the authority equals the functional
lookup. -/
theorem Ctx.LookupCVar.eq_authority {Γ : Ctx s} {c : BVar s .cvar}
    {a : Authority} {cb : CaptureBound s}
    (h : Ctx.LookupCVar Γ c a cb) : a = Γ.lookup_authority c := by
  induction h with
  | here => rfl
  | there _ ih => simp only [Ctx.lookup_authority, ih]

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
    | cvar _ cb => cases x with
      | there x' => simp only [lookup_tvar, lookup_tvar', lookup_tvar'_aux]

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
    | cvar _ cb => cases x with
      | there x' => simp only [lookup_var, lookup_var', lookup_var'_aux]

/-- The lookup equals the primed lookup renamed by succ. -/
theorem Ctx.lookup_cvar_eq (Γ : Ctx (s,,k)) (c : BVar (s,,k) .cvar) :
    Γ.lookup_cvar c = (Γ.lookup_cvar' c).rename Rename.succ := by
  cases Γ with
  | push Γ' b =>
    cases b with
    | tvar S => cases c with
      | there c' => simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]
    | var T => cases c with
      | there c' => simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]
    | cvar _ cb => cases c with
      | here => simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]
      | there c' => simp only [lookup_cvar, lookup_cvar', lookup_cvar'_aux]

mutual

/-- Helper: peak up a bound var in context. -/
def CaptureSet.peaksVarBound : (Γ : Ctx s) → (m : Access) → BVar s .var → CaptureSet s
| .push Γ (.var T), m, .here =>
    (CaptureSet.peaks Γ T.captureSet).rename Rename.succ |> .applyAccess m
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
theorem CaptureSet.peaksVarBound_peaksOnly (Γ : Ctx s) (m : Access) (x : BVar s .var) :
    (peaksVarBound Γ m x).PeaksOnly := by
  match Γ, x with
  | .push Γ (.var T), .here =>
    rw [CaptureSet.peaksVarBound]
    exact (CaptureSet.peaks_peaksOnly Γ T.captureSet).rename Rename.succ |>.applyAccess m
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

/-
RETIRED (2026-05-25): `lock` removed from `Ctx`. These lock-transparency
lemmas are kept here, commented out, for reference.

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
-/

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
        | cvar _ cb =>
          cases x with
          | there x' =>
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
      CaptureSet.applyAccess_applyRO]
  | .push Γ' _, .var m (.bound (.there x')) =>
    simp only [CaptureSet.applyRO, CaptureSet.peaks, CaptureSet.peaksVarBound]
    have ih := peaks_applyRO_comm Γ' (.var m (.bound x'))
    simp only [CaptureSet.applyRO, CaptureSet.peaks] at ih
    rw [ih, CaptureSet.applyRO_rename]
termination_by (sizeOf Γ, sizeOf C)

theorem CaptureSet.peaks_applyMut_comm {Γ : Ctx s} {C : CaptureSet s} {m : Mutability} :
  (C.applyMut m).peaks Γ = (C.peaks Γ).applyMut m := by
  cases m with
  | epsilon => simp only [CaptureSet.applyMut_epsilon]
  | ro =>
    simp only [CaptureSet.applyMut_ro]
    exact peaks_applyRO_comm Γ C

theorem CaptureSet.peaks_applyDrop_comm (Γ : Ctx s) (C : CaptureSet s) :
  C.applyDrop.peaks Γ = (C.peaks Γ).applyDrop := by
  match Γ, C with
  | _, .empty => simp only [CaptureSet.applyDrop, CaptureSet.peaks]
  | Γ, .union C1 C2 =>
    simp only [CaptureSet.applyDrop, CaptureSet.peaks]
    rw [peaks_applyDrop_comm Γ C1, peaks_applyDrop_comm Γ C2]
    rfl
  | _, .cvar _ _ => simp only [CaptureSet.applyDrop, CaptureSet.peaks]
  | _, .var _ (.free _) =>
    simp only [CaptureSet.applyDrop, CaptureSet.peaks]
    rfl
  | .push Γ' (.var T), .var m (.bound .here) =>
    simp only [CaptureSet.applyDrop, CaptureSet.peaks, CaptureSet.peaksVarBound,
      CaptureSet.applyAccess_drop, CaptureSet.applyAccess_applyDrop]
  | .push Γ' _, .var m (.bound (.there x')) =>
    simp only [CaptureSet.applyDrop, CaptureSet.peaks, CaptureSet.peaksVarBound]
    have ih := peaks_applyDrop_comm Γ' (.var m (.bound x'))
    simp only [CaptureSet.applyDrop, CaptureSet.peaks] at ih
    rw [ih, CaptureSet.applyDrop_rename]
termination_by (sizeOf Γ, sizeOf C)

theorem CaptureSet.peaks_applyAccess_comm {Γ : Ctx s} {C : CaptureSet s} {a : Access} :
  (C.applyAccess a).peaks Γ = (C.peaks Γ).applyAccess a := by
  cases a with
  | M m => simp only [CaptureSet.applyAccess_M]; exact peaks_applyMut_comm
  | drop => simp only [CaptureSet.applyAccess_drop]; exact peaks_applyDrop_comm Γ C

theorem CaptureSet.var_peaks {Γ : Ctx s}
  (hb : Γ.LookupVar x T) :
  (CaptureSet.peaks Γ (CaptureSet.var m (.bound x))) = (T.captureSet.applyAccess m).peaks Γ := by
  induction hb with
  | here =>
    simp only [CaptureSet.peaks, CaptureSet.peaksVarBound, Ty.captureSet_rename,
               peaks_rename_succ_eq, peaks_applyAccess_comm]
  | there hb' ih =>
    conv_lhs => unfold peaks peaksVarBound
    simp only [Ty.captureSet_rename]
    rw [show peaks _ (CaptureSet.var m (.bound _)) = peaksVarBound _ m _ from by
          unfold peaks; rfl] at ih
    rw [ih, ← CaptureSet.applyAccess_rename, ← peaks_rename_succ_eq]

/-- Sequential composition check on peak sets: using `P1` then `P2` is valid
when no peak consumed (`.drop`) in `P1` is used again in `P2` (no
use-after-consume). The combined authority is just `P1 ∪ P2`. -/
def PeakSet.SeqComp (P1 P2 : PeakSet s) : Prop :=
  ∀ (a : Access) (c : BVar s .cvar),
    (CaptureSet.cvar .drop c) ⊆ P1.cs → (CaptureSet.cvar a c) ⊆ P2.cs → False

/-- Sequential composition of capture sets in a context: expand to peaks, then
check the resulting peak sets compose. -/
def CaptureSet.SeqComp (Γ : Ctx s) (C1 C2 : CaptureSet s) : Prop :=
  PeakSet.SeqComp (C1.peakset Γ) (C2.peakset Γ)

/-- A peak set is *droppable* in `Γ` when every capture variable occurring in it
(at any access `a`) is bound with `can_drop` authority — i.e. each of its peaks
may legitimately be consumed. -/
def PeakSet.droppable (Γ : Ctx s) (P : PeakSet s) : Prop :=
  ∀ (a : Access) (c : BVar s .cvar),
    (CaptureSet.cvar a c) ⊆ P.cs → Γ.lookup_authority c = .can_drop

/-- A capture set is *droppable* in `Γ` when its peak set is droppable — i.e.
expand it to peaks, then check every capture variable peak is bound with
`can_drop` authority. -/
def CaptureSet.droppable (Γ : Ctx s) (C : CaptureSet s) : Prop :=
  PeakSet.droppable Γ (C.peakset Γ)

/-
RETIRED (2026-05-25): the access/consume machinery below was keyed on the
per-binding `UseMode` and on context `lock`s, both now removed. It is kept
here, commented out, for reference — access/consume is to be re-expressed via
the `Access` qualifier on capture references.

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

/-- The set of all peaks in the context that are at `.consume` mode and not locked. -/
def Ctx.consumeset : Ctx s -> PeakSet s
| .empty => ⟨.empty, .empty⟩
| .push Γ (.var _) => Γ.consumeset.rename Rename.succ
| .push Γ (.tvar _) => Γ.consumeset.rename Rename.succ
| .push Γ (.cvar .access _) => Γ.consumeset.rename Rename.succ
| .push Γ (.cvar .empty _) => Γ.consumeset.rename Rename.succ
| .push Γ (.cvar .consume _) =>
    let ps := Γ.consumeset.rename Rename.succ
    ⟨.union ps.cs (.cvar (.M .epsilon) .here), .union ps.h .cvar⟩
| .lock _ => ⟨.empty, .empty⟩

/-- The set of all peaks in the context that grant access — i.e., are at
    `.access` mode. Locks are transparent for accessibility (they only seal
    consume-mode peaks). A `.consume` cvar does *not* contribute here; its
    drop-authority is tracked separately in `consumeset`. -/
def Ctx.accessset : Ctx s -> PeakSet s
| .empty => ⟨.empty, .empty⟩
| .push Γ (.var _) => Γ.accessset.rename Rename.succ
| .push Γ (.tvar _) => Γ.accessset.rename Rename.succ
| .push Γ (.cvar .empty _) => Γ.accessset.rename Rename.succ
| .push Γ (.cvar .access _) =>
    let ps := Γ.accessset.rename Rename.succ
    ⟨.union ps.cs (.cvar (.M .epsilon) .here), .union ps.h .cvar⟩
| .push Γ (.cvar .consume _) => Γ.accessset.rename Rename.succ
| .lock Γ => Γ.accessset

/-- The set of all peaks in the context that are *used* — i.e., either at
    `.access` mode (accessible reads/writes) or at `.consume` mode (drops).
    Defined as the union of `accessset` and `consumeset`. -/
def Ctx.useset (Γ : Ctx s) : PeakSet s :=
  ⟨.union Γ.accessset.cs Γ.consumeset.cs,
   .union Γ.accessset.h Γ.consumeset.h⟩

/-- Sequential composition of use modes: `SeqComp m1 m2 m3` means using `m1`
first then `m2` yields `m3`. -/
inductive UseMode.SeqComp : UseMode -> UseMode -> UseMode -> Prop where
| l_empty :
  -------------------
  SeqComp .empty R R
| r_empty :
  -------------------
  SeqComp R .empty R
| access_access :
  SeqComp .access .access .access
| access_consume :
  SeqComp .access .consume .consume

/-- Pointwise lifting of `UseMode.SeqComp` to contexts: `SeqComp Γ1 Γ2 Γ3` means
`Γ1` and `Γ2` share the same shape and var/tvar bindings, with cvar use modes
related per-binding by `UseMode.SeqComp`. -/
inductive Ctx.SeqComp : Ctx s -> Ctx s -> Ctx s -> Prop where
| empty :
  -------------------
  SeqComp .empty .empty .empty
| push_var {Γ1 Γ2 Γ3 : Ctx s} {T : Ty .capt s} :
  SeqComp Γ1 Γ2 Γ3 ->
  -------------------
  SeqComp (Γ1.push (.var T)) (Γ2.push (.var T)) (Γ3.push (.var T))
| push_tvar {Γ1 Γ2 Γ3 : Ctx s} {S : PureTy s} :
  SeqComp Γ1 Γ2 Γ3 ->
  -------------------
  SeqComp (Γ1.push (.tvar S)) (Γ2.push (.tvar S)) (Γ3.push (.tvar S))
| push_cvar {Γ1 Γ2 Γ3 : Ctx s} {m1 m2 m3 : UseMode} {B : CaptureBound s} :
  SeqComp Γ1 Γ2 Γ3 ->
  UseMode.SeqComp m1 m2 m3 ->
  -------------------
  SeqComp (Γ1.push (.cvar m1 B)) (Γ2.push (.cvar m2 B)) (Γ3.push (.cvar m3 B))
| lock {Γ : Ctx s} :
  -------------------
  SeqComp Γ.lock Γ.lock Γ.lock

mutual
/-- `peaks` only consults var bindings, which `Ctx.SeqComp` preserves exactly,
so `peaks` is invariant under sequential composition (left). -/
theorem CaptureSet.peaks_seqcomp_eq
    {Γ1 Γ2 Γ : Ctx s} (h : Ctx.SeqComp Γ1 Γ2 Γ) (cs : CaptureSet s) :
    cs.peaks Γ = cs.peaks Γ1 := by
  match cs with
  | .empty => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .union cs1 cs2 =>
    rw [CaptureSet.peaks, CaptureSet.peaks,
        CaptureSet.peaks_seqcomp_eq h cs1,
        CaptureSet.peaks_seqcomp_eq h cs2]
  | .cvar _ _ => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .var _ (.free _) => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .var m (.bound x) =>
    rw [CaptureSet.peaks, CaptureSet.peaks]
    exact CaptureSet.peaksVarBound_seqcomp_eq h m x
termination_by (sizeOf Γ, sizeOf cs)

/-- `peaksVarBound` is invariant under sequential composition (left). -/
theorem CaptureSet.peaksVarBound_seqcomp_eq
    {Γ1 Γ2 Γ : Ctx s} (h : Ctx.SeqComp Γ1 Γ2 Γ) (m : Access) (x : BVar s .var) :
    peaksVarBound Γ m x = peaksVarBound Γ1 m x := by
  match h, x with
  | Ctx.SeqComp.push_var hsub, .here =>
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
        CaptureSet.peaks_seqcomp_eq hsub]
  | Ctx.SeqComp.push_var hsub, .there x' =>
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
        CaptureSet.peaksVarBound_seqcomp_eq hsub m x']
  | Ctx.SeqComp.push_tvar hsub, .there x' =>
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
        CaptureSet.peaksVarBound_seqcomp_eq hsub m x']
  | Ctx.SeqComp.push_cvar hsub _, .there x' =>
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
        CaptureSet.peaksVarBound_seqcomp_eq hsub m x']
  | Ctx.SeqComp.lock, x => rfl
termination_by (sizeOf Γ, sizeOf x + 1)
end

/-- `peakset` is invariant under sequential composition (left). -/
theorem CaptureSet.peakset_seqcomp_eq
    {Γ1 Γ2 Γ : Ctx s} (h : Ctx.SeqComp Γ1 Γ2 Γ) (cs : CaptureSet s) :
    cs.peakset Γ = cs.peakset Γ1 := by
  unfold CaptureSet.peakset
  congr 1
  exact CaptureSet.peaks_seqcomp_eq h cs

mutual
/-- `peaks` is invariant under sequential composition (right). -/
theorem CaptureSet.peaks_seqcomp_eq_right
    {Γ1 Γ2 Γ : Ctx s} (h : Ctx.SeqComp Γ1 Γ2 Γ) (cs : CaptureSet s) :
    cs.peaks Γ = cs.peaks Γ2 := by
  match cs with
  | .empty => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .union cs1 cs2 =>
    rw [CaptureSet.peaks, CaptureSet.peaks,
        CaptureSet.peaks_seqcomp_eq_right h cs1,
        CaptureSet.peaks_seqcomp_eq_right h cs2]
  | .cvar _ _ => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .var _ (.free _) => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .var m (.bound x) =>
    rw [CaptureSet.peaks, CaptureSet.peaks]
    exact CaptureSet.peaksVarBound_seqcomp_eq_right h m x
termination_by (sizeOf Γ, sizeOf cs)

/-- `peaksVarBound` is invariant under sequential composition (right). -/
theorem CaptureSet.peaksVarBound_seqcomp_eq_right
    {Γ1 Γ2 Γ : Ctx s} (h : Ctx.SeqComp Γ1 Γ2 Γ) (m : Access) (x : BVar s .var) :
    peaksVarBound Γ m x = peaksVarBound Γ2 m x := by
  match h, x with
  | Ctx.SeqComp.push_var hsub, .here =>
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
        CaptureSet.peaks_seqcomp_eq_right hsub]
  | Ctx.SeqComp.push_var hsub, .there x' =>
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
        CaptureSet.peaksVarBound_seqcomp_eq_right hsub m x']
  | Ctx.SeqComp.push_tvar hsub, .there x' =>
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
        CaptureSet.peaksVarBound_seqcomp_eq_right hsub m x']
  | Ctx.SeqComp.push_cvar hsub _, .there x' =>
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound,
        CaptureSet.peaksVarBound_seqcomp_eq_right hsub m x']
  | Ctx.SeqComp.lock, x => rfl
termination_by (sizeOf Γ, sizeOf x + 1)
end

/-- `peakset` is invariant under sequential composition (right). -/
theorem CaptureSet.peakset_seqcomp_eq_right
    {Γ1 Γ2 Γ : Ctx s} (h : Ctx.SeqComp Γ1 Γ2 Γ) (cs : CaptureSet s) :
    cs.peakset Γ = cs.peakset Γ2 := by
  unfold CaptureSet.peakset
  congr 1
  exact CaptureSet.peaks_seqcomp_eq_right h cs
-/

end Consume
