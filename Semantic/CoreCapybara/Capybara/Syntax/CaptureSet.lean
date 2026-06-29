import Semantic.CoreCapybara.Syntax.CaptureSet

/-!
# Capybara (source-language) capture sets

`CapyCaptureSet` is a fork of the Core `CaptureSet` for the Capybara *source*
language.  Forking lets us add source-only constructs — notably `pseudo_peak`,
which halts the `peaks` computation at a substituted-in capture so that `peaks`
commutes with capture substitution — without perturbing the target calculus.

`Var`, `Access`, `Mutability`, `Var.rename`, and `Var.IsClosed` are shared with
Core (imported above); only the capture-set type, its peak sets, and their
operations are duplicated here.
-/

namespace CoreCapybara

inductive CapyCaptureSet : Sig -> Type where
| empty : CapyCaptureSet s
| union : CapyCaptureSet s -> CapyCaptureSet s -> CapyCaptureSet s
| var : Access -> Var .var s -> CapyCaptureSet s
| cvar : Access -> BVar s .cvar -> CapyCaptureSet s
/-- A **pseudo-peak**: a capture set that `peaks` HALTS at (treating it as a single
    frozen peak instead of recursing into its content).  It is a source-only
    construct — the target `CaptureSet` has no counterpart — introduced so that
    `peaks` commutes with capture substitution: substituting a capture variable
    `c ↦ D` produces one frozen `pseudo_peak D` rather than expanding `D`'s atoms
    into the surrounding peak set (which is what merged/un-merged the lock items
    differently and blocked B2c). -/
| pseudo_peak : CapyCaptureSet s -> CapyCaptureSet s

/-- Provides `{}` notation for the empty capture set. -/
@[simp]
instance CapyCaptureSet.instEmptyCollection :
  EmptyCollection (CapyCaptureSet s) where
  emptyCollection := CapyCaptureSet.empty

/-- Provides `∪` notation for capture set union. -/
@[simp]
instance CapyCaptureSet.instUnion : Union (CapyCaptureSet s) where
  union := CapyCaptureSet.union


/-- Applies a renaming to all bound variables in a capture set. -/
def CapyCaptureSet.rename : CapyCaptureSet s1 -> Rename s1 s2 -> CapyCaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, ρ => .union (cs1.rename ρ) (cs2.rename ρ)
| .var m x, ρ => .var m (x.rename ρ)
| .cvar m x, ρ => .cvar m (ρ.var x)
| .pseudo_peak C, ρ => .pseudo_peak (C.rename ρ)

/-- Renaming by the identity renaming leaves a capture set unchanged. -/
theorem CapyCaptureSet.rename_id {cs : CapyCaptureSet s} :
    cs.rename (Rename.id) = cs := by
  induction cs
  case empty => rfl
  case union ih1 ih2 => simp [CapyCaptureSet.rename, ih1, ih2]
  case var m x => cases x <;> rfl
  case cvar m x => simp [CapyCaptureSet.rename, Rename.id]
  case pseudo_peak C ih => simp [CapyCaptureSet.rename, ih]

/-- Renaming distributes over composition of renamings. -/
theorem CapyCaptureSet.rename_comp {cs : CapyCaptureSet s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cs.rename f).rename g = cs.rename (f.comp g) := by
  induction cs generalizing s2 s3
  case empty => rfl
  case union ih1 ih2 => simp [CapyCaptureSet.rename, ih1, ih2]
  case var m x =>
    cases x
    · simp [CapyCaptureSet.rename, Var.rename]; rfl
    · simp [CapyCaptureSet.rename, Var.rename]
  case cvar m x => simp [CapyCaptureSet.rename, Rename.comp]
  case pseudo_peak C ih => simp [CapyCaptureSet.rename, ih]

/-- Applies read-only mutability to all elements in a capture set. -/
def CapyCaptureSet.applyRO : CapyCaptureSet s -> CapyCaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.applyRO) (cs2.applyRO)
| .var a x => .var a.applyRO x
| .cvar a x => .cvar a.applyRO x
| .pseudo_peak C => .pseudo_peak C.applyRO

/-- Applies a mutability to all elements in a capture set.
  This is used to preserve mutability during substitution. -/
def CapyCaptureSet.applyMut (m : Mutability) (cs : CapyCaptureSet s) : CapyCaptureSet s :=
  match m with
  | .epsilon => cs
  | .ro => cs.applyRO

@[simp] theorem CapyCaptureSet.applyRO_empty : (CapyCaptureSet.empty (s:=s)).applyRO = .empty := rfl
@[simp] theorem CapyCaptureSet.applyRO_union {cs1 cs2 : CapyCaptureSet s} :
    (cs1.union cs2).applyRO = cs1.applyRO.union cs2.applyRO := rfl
@[simp] theorem CapyCaptureSet.applyRO_var {a : Access} {x : Var .var s} :
    (CapyCaptureSet.var a x).applyRO = .var a.applyRO x := rfl
@[simp] theorem CapyCaptureSet.applyRO_cvar {a : Access} {x : BVar s .cvar} :
    (CapyCaptureSet.cvar a x).applyRO = .cvar a.applyRO x := rfl

@[simp] theorem CapyCaptureSet.applyMut_epsilon {cs : CapyCaptureSet s} :
    cs.applyMut .epsilon = cs := rfl
@[simp] theorem CapyCaptureSet.applyMut_ro {cs : CapyCaptureSet s} :
    cs.applyMut .ro = cs.applyRO := rfl

/-- Applying applyRO twice is idempotent. -/
@[simp]
theorem CapyCaptureSet.applyRO_applyRO {cs : CapyCaptureSet s} :
    cs.applyRO.applyRO = cs.applyRO := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [ih1, ih2, CapyCaptureSet.applyRO_union]
  | var a x => simp only [CapyCaptureSet.applyRO, Access.applyRO_idempotent]
  | cvar a x => simp only [CapyCaptureSet.applyRO, Access.applyRO_idempotent]
  | pseudo_peak C ih => simp only [CapyCaptureSet.applyRO, ih]

/-- Applying applyMut after applyRO simplifies. -/
@[simp]
theorem CapyCaptureSet.applyRO_applyMut {cs : CapyCaptureSet s} {m : Mutability} :
    cs.applyRO.applyMut m = cs.applyRO := by
  cases m <;>
    simp only [CapyCaptureSet.applyMut_epsilon, CapyCaptureSet.applyMut_ro, applyRO_applyRO]

/-- Applying applyRO after applyMut gives applyRO. -/
@[simp]
theorem CapyCaptureSet.applyMut_applyRO {cs : CapyCaptureSet s} {m : Mutability} :
    (cs.applyMut m).applyRO = cs.applyRO := by
  cases m <;>
    simp only [CapyCaptureSet.applyMut_epsilon, CapyCaptureSet.applyMut_ro, applyRO_applyRO]

/-- applyRO distributes over rename. -/
theorem CapyCaptureSet.applyRO_rename {cs : CapyCaptureSet s1} {f : Rename s1 s2} :
    cs.applyRO.rename f = (cs.rename f).applyRO := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO_union, CapyCaptureSet.rename, ih1, ih2]
  | var a x => simp only [CapyCaptureSet.rename, CapyCaptureSet.applyRO]
  | cvar a x => simp only [CapyCaptureSet.rename, CapyCaptureSet.applyRO]
  | pseudo_peak C ih => simp only [CapyCaptureSet.rename, CapyCaptureSet.applyRO, ih]

/-- applyMut distributes over rename. -/
theorem CapyCaptureSet.applyMut_rename {cs : CapyCaptureSet s1} {f : Rename s1 s2}
    {m : Mutability} :
    (cs.applyMut m).rename f = (cs.rename f).applyMut m := by
  cases m <;>
    simp only [CapyCaptureSet.applyMut_epsilon, CapyCaptureSet.applyMut_ro, applyRO_rename]

/-- Sets every element of a capture set to `drop` mode. -/
def CapyCaptureSet.applyDrop : CapyCaptureSet s -> CapyCaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.applyDrop) (cs2.applyDrop)
| .var _ x => .var .drop x
| .cvar _ x => .cvar .drop x
| .pseudo_peak C => .pseudo_peak C.applyDrop

/-- Applies an access mode to all elements: a mutability acts via `applyMut`,
    while `drop` sets every element to `drop` mode via `applyDrop`. -/
def CapyCaptureSet.applyAccess (a : Access) (cs : CapyCaptureSet s) : CapyCaptureSet s :=
  match a with
  | .M m => cs.applyMut m
  | .drop => cs.applyDrop

@[simp] theorem CapyCaptureSet.applyAccess_M {m : Mutability} {cs : CapyCaptureSet s} :
    cs.applyAccess (.M m) = cs.applyMut m := rfl
@[simp] theorem CapyCaptureSet.applyAccess_drop {cs : CapyCaptureSet s} :
    cs.applyAccess .drop = cs.applyDrop := rfl

/-- Filters a capture set to its consumed *peaks* — capture variables held at
    `.drop` access mode. Access-mode peaks and variable atoms are discarded;
    resolve through a context with `CapyCaptureSet.peaks` first to account for
    consumed variables. -/
def CapyCaptureSet.consumed : CapyCaptureSet s -> CapyCaptureSet s
| .empty => .empty
| .union cs1 cs2 => .union (cs1.consumed) (cs2.consumed)
| .cvar .drop c => .cvar .drop c
| .cvar (.M _) _ => .empty
| .var _ _ => .empty
| .pseudo_peak C => .pseudo_peak C.consumed

/-- applyDrop distributes over rename. -/
theorem CapyCaptureSet.applyDrop_rename {cs : CapyCaptureSet s1} {f : Rename s1 s2} :
    cs.applyDrop.rename f = (cs.rename f).applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.rename, ih1, ih2]
  | var _ x => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.rename]
  | cvar _ x => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.rename]
  | pseudo_peak C ih => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.rename, ih]

/-- applyAccess distributes over rename. -/
theorem CapyCaptureSet.applyAccess_rename {cs : CapyCaptureSet s1} {f : Rename s1 s2} {a : Access} :
    (cs.applyAccess a).rename f = (cs.rename f).applyAccess a := by
  cases a with
  | M m => simp only [CapyCaptureSet.applyAccess_M, applyMut_rename]
  | drop => simp only [CapyCaptureSet.applyAccess_drop, applyDrop_rename]

/-- applyRO leaves a dropped capture set unchanged (`drop` is fixed under applyRO). -/
@[simp] theorem CapyCaptureSet.applyDrop_applyRO {cs : CapyCaptureSet s} :
    cs.applyDrop.applyRO = cs.applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.applyRO, ih1, ih2]
  | var _ x => rfl
  | cvar _ x => rfl
  | pseudo_peak C ih => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.applyRO, ih]

/-- applyRO commutes with applyAccess by reading off the read-only image of the mode. -/
theorem CapyCaptureSet.applyAccess_applyRO {cs : CapyCaptureSet s} {a : Access} :
    (cs.applyAccess a).applyRO = cs.applyAccess a.applyRO := by
  cases a with
  | M m =>
    cases m with
    | epsilon =>
      simp only [CapyCaptureSet.applyAccess_M, Access.applyRO, applyMut_epsilon, applyMut_ro]
    | ro =>
      simp only [CapyCaptureSet.applyAccess_M, Access.applyRO, applyMut_ro, applyRO_applyRO]
  | drop => simp only [CapyCaptureSet.applyAccess_drop, Access.applyRO, applyDrop_applyRO]

/-- applyDrop overwrites every mode, so it absorbs a preceding applyRO. -/
@[simp] theorem CapyCaptureSet.applyRO_applyDrop {cs : CapyCaptureSet s} :
    cs.applyRO.applyDrop = cs.applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CapyCaptureSet.applyRO, CapyCaptureSet.applyDrop, ih1, ih2]
  | var _ x => rfl
  | cvar _ x => rfl
  | pseudo_peak C ih => simp only [CapyCaptureSet.applyRO, CapyCaptureSet.applyDrop, ih]

/-- applyDrop is idempotent. -/
@[simp] theorem CapyCaptureSet.applyDrop_applyDrop {cs : CapyCaptureSet s} :
    cs.applyDrop.applyDrop = cs.applyDrop := by
  induction cs with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 => simp only [CapyCaptureSet.applyDrop, ih1, ih2]
  | var _ x => rfl
  | cvar _ x => rfl
  | pseudo_peak C ih => simp only [CapyCaptureSet.applyDrop, ih]

/-- applyDrop absorbs a preceding applyAccess (it overwrites every mode). -/
@[simp] theorem CapyCaptureSet.applyAccess_applyDrop {cs : CapyCaptureSet s} {a : Access} :
    (cs.applyAccess a).applyDrop = cs.applyDrop := by
  cases a with
  | M m =>
    cases m with
    | epsilon => simp only [CapyCaptureSet.applyAccess_M, applyMut_epsilon]
    | ro => simp only [CapyCaptureSet.applyAccess_M, applyMut_ro, applyRO_applyDrop]
  | drop => simp only [CapyCaptureSet.applyAccess_drop, applyDrop_applyDrop]

/-- The subset relation on capture sets. -/
inductive CapyCaptureSet.Subset : CapyCaptureSet s -> CapyCaptureSet s -> Prop where
| refl :
  --------------------
  Subset C C
| empty :
  --------------------
  Subset .empty C
| union_left :
  Subset C1 C ->
  Subset C2 C ->
  --------------------
  Subset (C1.union C2) C
| union_right_left :
  Subset C C1 ->
  --------------------
  Subset C (C1.union C2)
| union_right_right {C1 : CapyCaptureSet s} :
  Subset C C2 ->
  --------------------
  Subset C (C1.union C2)

/-- Provides `⊆` notation for capture set subset. -/
instance CapyCaptureSet.instHasSubset : HasSubset (CapyCaptureSet s) where
  Subset := CapyCaptureSet.Subset


/-- A capture set is closed if it contains no heap pointers. -/
inductive CapyCaptureSet.IsClosed : CapyCaptureSet s -> Prop where
| empty : CapyCaptureSet.IsClosed .empty
| union : CapyCaptureSet.IsClosed cs1 -> CapyCaptureSet.IsClosed cs2 ->
    CapyCaptureSet.IsClosed (cs1.union cs2)
| cvar : CapyCaptureSet.IsClosed (.cvar m x)
| var_bound : CapyCaptureSet.IsClosed (.var m (.bound x))
| pseudo_peak : CapyCaptureSet.IsClosed C -> CapyCaptureSet.IsClosed (.pseudo_peak C)

/-- applyRO preserves closedness. -/
theorem CapyCaptureSet.applyRO_isClosed {cs : CapyCaptureSet s}
    (hc : cs.IsClosed) : cs.applyRO.IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | var m' x =>
    cases hc with | var_bound =>
    exact IsClosed.var_bound
  | cvar m' c =>
    exact IsClosed.cvar
  | pseudo_peak C ih =>
    cases hc with | pseudo_peak h =>
    exact IsClosed.pseudo_peak (ih h)

/-- applyMut preserves closedness. -/
theorem CapyCaptureSet.applyMut_isClosed {cs : CapyCaptureSet s} {m : Mutability}
    (hc : cs.IsClosed) : (cs.applyMut m).IsClosed := by
  cases m
  · exact hc
  · exact applyRO_isClosed hc

/-- applyDrop preserves closedness. -/
theorem CapyCaptureSet.applyDrop_isClosed {cs : CapyCaptureSet s}
    (hc : cs.IsClosed) : cs.applyDrop.IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 => exact IsClosed.union (ih1 h1) (ih2 h2)
  | var m' x =>
    cases hc with | var_bound => exact IsClosed.var_bound
  | cvar m' c => exact IsClosed.cvar
  | pseudo_peak C ih => cases hc with | pseudo_peak h => exact IsClosed.pseudo_peak (ih h)

/-- applyAccess preserves closedness. -/
theorem CapyCaptureSet.applyAccess_isClosed {cs : CapyCaptureSet s} {a : Access}
    (hc : cs.IsClosed) : (cs.applyAccess a).IsClosed := by
  cases a with
  | M m => exact applyMut_isClosed hc
  | drop => exact applyDrop_isClosed hc

/-- Renaming preserves closedness of a capture set. -/
theorem CapyCaptureSet.rename_isClosed {cs : CapyCaptureSet s1} {f : Rename s1 s2}
    (hc : cs.IsClosed) : (cs.rename f).IsClosed := by
  induction cs with
  | empty => exact IsClosed.empty
  | union cs1 cs2 ih1 ih2 =>
    cases hc with | union h1 h2 =>
    simp only [CapyCaptureSet.rename]
    exact IsClosed.union (ih1 h1) (ih2 h2)
  | var m' x =>
    cases hc with | var_bound =>
    simp only [CapyCaptureSet.rename, Var.rename]
    exact IsClosed.var_bound
  | cvar m' c =>
    simp only [CapyCaptureSet.rename]
    exact IsClosed.cvar
  | pseudo_peak C ih =>
    cases hc with | pseudo_peak h =>
    simp only [CapyCaptureSet.rename]
    exact IsClosed.pseudo_peak (ih h)

/-- Whether a capture set contains only peaks (capture variables). -/
inductive CapyCaptureSet.PeaksOnly : CapyCaptureSet s -> Prop where
| empty :
  ---------------------
  PeaksOnly .empty
| union {C1 C2 : CapyCaptureSet s} :
  PeaksOnly C1 ->
  PeaksOnly C2 ->
  ---------------------
  PeaksOnly (C1.union C2)
| cvar {m : Access} {c : BVar s .cvar} :
  ---------------------
  PeaksOnly (.cvar m c)
| pseudo_peak {C : CapyCaptureSet s} :
  ---------------------
  PeaksOnly (.pseudo_peak C)

/-- A capture set contains no `pseudo_peak`.  Frozen peaks are a substitution
    artifact (never surface syntax); the LOCK bridge lemmas (`compile_peaksOnly`,
    the `peakItem`/`peakCvars` machinery) and the resolving `resourcePeaks` all
    operate on `NoPseudoPeak` sets, where the `pseudo_peak` case is unreachable. -/
inductive CapyCaptureSet.NoPseudoPeak : CapyCaptureSet s -> Prop where
| empty :
  NoPseudoPeak .empty
| union {C1 C2 : CapyCaptureSet s} :
  NoPseudoPeak C1 -> NoPseudoPeak C2 -> NoPseudoPeak (C1.union C2)
| cvar {m : Access} {c : BVar s .cvar} :
  NoPseudoPeak (.cvar m c)
| var {m : Access} {x : Var .var s} :
  NoPseudoPeak (.var m x)

/-- `NoPseudoPeak` is preserved under renaming. -/
theorem CapyCaptureSet.NoPseudoPeak.rename {cs : CapyCaptureSet s} (h : cs.NoPseudoPeak)
    (ρ : Rename s s') : (cs.rename ρ).NoPseudoPeak := by
  induction h with
  | empty => exact NoPseudoPeak.empty
  | union _ _ ih1 ih2 => exact NoPseudoPeak.union ih1 ih2
  | cvar => exact NoPseudoPeak.cvar
  | var => exact NoPseudoPeak.var

/-- `NoPseudoPeak` is preserved under `applyAccess` (it never introduces a frozen peak). -/
theorem CapyCaptureSet.NoPseudoPeak.applyAccess {cs : CapyCaptureSet s} (h : cs.NoPseudoPeak)
    {a : Access} : (cs.applyAccess a).NoPseudoPeak := by
  induction h with
  | empty =>
    cases a with
    | M m => cases m <;> exact NoPseudoPeak.empty
    | drop => exact NoPseudoPeak.empty
  | union _ _ ih1 ih2 =>
    cases a with
    | M m => cases m <;> exact NoPseudoPeak.union ih1 ih2
    | drop => exact NoPseudoPeak.union ih1 ih2
  | cvar =>
    cases a with
    | M m => cases m <;> exact NoPseudoPeak.cvar
    | drop => exact NoPseudoPeak.cvar
  | var =>
    cases a with
    | M m => cases m <;> exact NoPseudoPeak.var
    | drop => exact NoPseudoPeak.var

/-- Erases all access modes (sets every atom to `.M .epsilon`), giving the
    mode-independent *identity* of a capture set.  Two frozen-peak items that
    differ only by the access mode folded in during substitution
    (`pseudo_peak (D.applyAccess aᵢ)`) share a `modeErase`d base, so the lock can
    group them as a single peak (avoiding a spurious `⟦D⟧ ⊥ ⟦D⟧` self-separation). -/
def CapyCaptureSet.modeErase : CapyCaptureSet s -> CapyCaptureSet s
| .empty => .empty
| .union c1 c2 => .union c1.modeErase c2.modeErase
| .var _ x => .var (.M .epsilon) x
| .cvar _ c => .cvar (.M .epsilon) c
| .pseudo_peak C => .pseudo_peak C.modeErase

/-- `modeErase` absorbs a preceding `applyRO` (both only touch access modes). -/
@[simp] theorem CapyCaptureSet.modeErase_applyRO {cs : CapyCaptureSet s} :
    cs.applyRO.modeErase = cs.modeErase := by
  induction cs with
  | empty => rfl
  | union c1 c2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO_union, CapyCaptureSet.modeErase, ih1, ih2]
  | var a x => rfl
  | cvar a x => rfl
  | pseudo_peak C ih => simp only [CapyCaptureSet.applyRO, CapyCaptureSet.modeErase, ih]

/-- `modeErase` absorbs a preceding `applyDrop`. -/
@[simp] theorem CapyCaptureSet.modeErase_applyDrop {cs : CapyCaptureSet s} :
    cs.applyDrop.modeErase = cs.modeErase := by
  induction cs with
  | empty => rfl
  | union c1 c2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.modeErase, ih1, ih2]
  | var a x => rfl
  | cvar a x => rfl
  | pseudo_peak C ih => simp only [CapyCaptureSet.applyDrop, CapyCaptureSet.modeErase, ih]

/-- `modeErase` absorbs a preceding `applyAccess` — the grouping key is
    mode-independent. -/
@[simp] theorem CapyCaptureSet.modeErase_applyAccess {cs : CapyCaptureSet s} {a : Access} :
    (cs.applyAccess a).modeErase = cs.modeErase := by
  cases a with
  | M m => cases m with
    | epsilon => rfl
    | ro => simp only [CapyCaptureSet.applyAccess_M, CapyCaptureSet.applyMut_ro,
        CapyCaptureSet.modeErase_applyRO]
  | drop => simp only [CapyCaptureSet.applyAccess_drop, CapyCaptureSet.modeErase_applyDrop]

/-- `modeErase` is idempotent. -/
@[simp] theorem CapyCaptureSet.modeErase_idem {cs : CapyCaptureSet s} :
    cs.modeErase.modeErase = cs.modeErase := by
  induction cs with
  | empty => rfl
  | union c1 c2 ih1 ih2 => simp only [CapyCaptureSet.modeErase, ih1, ih2]
  | var a x => rfl
  | cvar a x => rfl
  | pseudo_peak C ih => simp only [CapyCaptureSet.modeErase, ih]

/-- `modeErase` commutes with renaming. -/
theorem CapyCaptureSet.modeErase_rename {cs : CapyCaptureSet s1} {ρ : Rename s1 s2} :
    (cs.rename ρ).modeErase = cs.modeErase.rename ρ := by
  induction cs generalizing s2 with
  | empty => rfl
  | union c1 c2 ih1 ih2 => simp only [CapyCaptureSet.rename, CapyCaptureSet.modeErase, ih1, ih2]
  | var a x => rfl
  | cvar a x => rfl
  | pseudo_peak C ih => simp only [CapyCaptureSet.rename, CapyCaptureSet.modeErase, ih]

structure CapyPeakSet (s : Sig) where
  cs : CapyCaptureSet s
  h : cs.PeaksOnly

/-- PeaksOnly is preserved under renaming. -/
theorem CapyCaptureSet.PeaksOnly.rename {cs : CapyCaptureSet s} (h : cs.PeaksOnly)
    (ρ : Rename s s') : (cs.rename ρ).PeaksOnly := by
  induction h with
  | empty => exact PeaksOnly.empty
  | union _ _ ih1 ih2 => exact PeaksOnly.union ih1 ih2
  | cvar => exact PeaksOnly.cvar
  | pseudo_peak => exact PeaksOnly.pseudo_peak

-- NOTE: `PeaksOnly → IsClosed` no longer holds: `pseudo_peak C` is `PeaksOnly`
-- unconditionally (a frozen peak is a peak) but is closed only when `C` is.  The
-- old `CapyCaptureSet.PeaksOnly.isClosed` theorem (unused) is therefore dropped.

/-- PeaksOnly is preserved under applyRO. -/
theorem CapyCaptureSet.PeaksOnly.applyRO {cs : CapyCaptureSet s} (h : cs.PeaksOnly) :
    cs.applyRO.PeaksOnly := by
  induction h with
  | empty => exact PeaksOnly.empty
  | union _ _ ih1 ih2 => exact PeaksOnly.union ih1 ih2
  | cvar => exact PeaksOnly.cvar
  | pseudo_peak => exact PeaksOnly.pseudo_peak

/-- PeaksOnly is preserved under applyMut. -/
theorem CapyCaptureSet.PeaksOnly.applyMut {cs : CapyCaptureSet s} (h : cs.PeaksOnly)
    (m : Mutability) : (cs.applyMut m).PeaksOnly := by
  cases m with
  | epsilon => exact h
  | ro => exact h.applyRO

/-- PeaksOnly is preserved under applyDrop. -/
theorem CapyCaptureSet.PeaksOnly.applyDrop {cs : CapyCaptureSet s} (h : cs.PeaksOnly) :
    cs.applyDrop.PeaksOnly := by
  induction h with
  | empty => exact PeaksOnly.empty
  | union _ _ ih1 ih2 => exact PeaksOnly.union ih1 ih2
  | cvar => exact PeaksOnly.cvar
  | pseudo_peak => exact PeaksOnly.pseudo_peak

/-- PeaksOnly is preserved under applyAccess. -/
theorem CapyCaptureSet.PeaksOnly.applyAccess {cs : CapyCaptureSet s} (h : cs.PeaksOnly)
    (a : Access) : (cs.applyAccess a).PeaksOnly := by
  cases a with
  | M m => exact h.applyMut m
  | drop => exact h.applyDrop

def CapyPeakSet.rename {s1 s2 : Sig} (ps : CapyPeakSet s1) (ρ : Rename s1 s2) : CapyPeakSet s2 :=
  ⟨ps.cs.rename ρ, ps.h.rename ρ⟩

/-- Filtering to consumed peaks preserves `PeaksOnly`. -/
theorem CapyCaptureSet.PeaksOnly.consumed {cs : CapyCaptureSet s} (h : cs.PeaksOnly) :
    cs.consumed.PeaksOnly := by
  induction h with
  | empty => exact PeaksOnly.empty
  | union _ _ ih1 ih2 => exact PeaksOnly.union ih1 ih2
  | cvar =>
    rename_i m c
    cases m with
    | M _ => exact PeaksOnly.empty
    | drop => exact PeaksOnly.cvar
  | pseudo_peak => exact PeaksOnly.pseudo_peak

/-- The consumed (`.drop`-mode) peaks of a peak set. -/
def CapyPeakSet.consumed (P : CapyPeakSet s) : CapyPeakSet s :=
  ⟨P.cs.consumed, P.h.consumed⟩

/-- Whether this capture set is equivalent to an empty set. -/
inductive CapyCaptureSet.IsEmpty : CapyCaptureSet s -> Prop where
| empty :
  ----------------
  IsEmpty .empty
| union :
  IsEmpty cs1 ->
  IsEmpty cs2 ->
  ----------------
  IsEmpty (cs1.union cs2)

/-- Renaming preserves emptiness. -/
theorem CapyCaptureSet.IsEmpty.rename {cs : CapyCaptureSet s1} (h : cs.IsEmpty) (ρ : Rename s1 s2) :
    (cs.rename ρ).IsEmpty := by
  induction h with
  | empty => exact IsEmpty.empty
  | union _ _ ih1 ih2 => exact IsEmpty.union ih1 ih2

/-- Covering relation on capture sets: a mutability-aware subset where a set may be
    covered by the same set at a weaker (`≤`) mutability. -/
inductive CapyCaptureSet.CoveredBy : CapyCaptureSet s -> CapyCaptureSet s -> Prop where
| refl {C : CapyCaptureSet s} {m1 m2 : Mutability} :
  (hm : m1 ≤ m2) ->
  --------------------
  CoveredBy (C.applyMut m1) (C.applyMut m2)
| empty :
  --------------------
  CoveredBy .empty C
| union_left :
  CoveredBy C1 C ->
  CoveredBy C2 C ->
  --------------------
  CoveredBy (C1.union C2) C
| union_right_left :
  CoveredBy C C1 ->
  --------------------
  CoveredBy C (C1.union C2)
| union_right_right {C1 : CapyCaptureSet s} :
  CoveredBy C C2 ->
  --------------------
  CoveredBy C (C1.union C2)

namespace CapyCaptureSet.CoveredBy

/-- Reflexivity of `CoveredBy`: any `C` covers itself. -/
theorem refl' {C : CapyCaptureSet s} : C.CoveredBy C := by
  have h : (C.applyMut .epsilon).CoveredBy (C.applyMut .epsilon) := .refl Mutability.Le.refl
  simp only [CapyCaptureSet.applyMut_epsilon] at h
  exact h

theorem mut_mono_left {C1 C2 : CapyCaptureSet s} {m1 m2 : Mutability}
  (hm : m1 ≤ m2)
  (hsub : CapyCaptureSet.CoveredBy (C1.applyMut m2) C2) :
    CapyCaptureSet.CoveredBy (C1.applyMut m1) C2 := by
  cases hm with
  | refl => exact hsub
  | ro_eps =>
    simp only [CapyCaptureSet.applyMut_epsilon] at hsub
    simp only [CapyCaptureSet.applyMut_ro]
    induction hsub with
    | refl hm' =>
      simp only [CapyCaptureSet.applyMut_applyRO]
      exact .refl Mutability.Le.ro_le
    | empty =>
      simp only [CapyCaptureSet.applyRO]
      exact .empty
    | union_left _ _ ih1 ih2 =>
      simp only [CapyCaptureSet.applyRO]
      exact .union_left ih1 ih2
    | union_right_left _ ih =>
      exact .union_right_left ih
    | union_right_right _ ih =>
      exact .union_right_right ih

private theorem union_coveredby_left_aux {AB A B C : CapyCaptureSet s}
  (he : A.union B = AB)
  (h : AB.CoveredBy C) : A.CoveredBy C := by
  induction h generalizing A B with
  | refl hm =>
    rename_i D m1 m2
    cases m1 with
    | epsilon =>
      simp only [CapyCaptureSet.applyMut_epsilon] at he
      subst he
      cases hm with
      | refl =>
        simp only [CapyCaptureSet.applyMut_epsilon]
        exact .union_right_left refl'
    | ro =>
      simp only [CapyCaptureSet.applyMut_ro] at he
      cases D with
      | empty =>
        simp only [CapyCaptureSet.applyRO] at he
        contradiction
      | union D1 D2 =>
        simp only [CapyCaptureSet.applyRO] at he
        injection he with hA hB
        subst hA
        cases m2 with
        | epsilon =>
          simp only [CapyCaptureSet.applyMut_epsilon]
          have h1 : D1.applyRO.CoveredBy D1 := .refl Mutability.Le.ro_eps
          exact .union_right_left h1
        | ro =>
          simp only [CapyCaptureSet.applyMut_ro, CapyCaptureSet.applyRO]
          exact .union_right_left refl'
      | var m x =>
        simp only [CapyCaptureSet.applyRO] at he
        contradiction
      | cvar m c =>
        simp only [CapyCaptureSet.applyRO] at he
        contradiction
      | pseudo_peak D =>
        simp only [CapyCaptureSet.applyRO] at he
        contradiction
  | empty =>
    contradiction
  | union_left h1 _ _ _ =>
    injection he with hA _
    subst hA
    exact h1
  | union_right_left _ ih =>
    exact .union_right_left (ih he)
  | union_right_right _ ih =>
    exact .union_right_right (ih he)

/-- If a union is covered by `C`, so is its left component. -/
theorem union_coveredby_left {A B C : CapyCaptureSet s}
  (h : (A ∪ B).CoveredBy C) : A.CoveredBy C :=
  union_coveredby_left_aux rfl h

private theorem union_coveredby_right_aux {AB A B C : CapyCaptureSet s}
  (he : A.union B = AB)
  (h : AB.CoveredBy C) : B.CoveredBy C := by
  induction h generalizing A B with
  | refl hm =>
    rename_i D m1 m2
    cases m1 with
    | epsilon =>
      simp only [CapyCaptureSet.applyMut_epsilon] at he
      subst he
      cases hm with
      | refl =>
        simp only [CapyCaptureSet.applyMut_epsilon]
        exact .union_right_right refl'
    | ro =>
      simp only [CapyCaptureSet.applyMut_ro] at he
      cases D with
      | empty =>
        simp only [CapyCaptureSet.applyRO] at he
        contradiction
      | union D1 D2 =>
        simp only [CapyCaptureSet.applyRO] at he
        injection he with _ hB
        subst hB
        cases m2 with
        | epsilon =>
          simp only [CapyCaptureSet.applyMut_epsilon]
          have h1 : D2.applyRO.CoveredBy D2 := .refl Mutability.Le.ro_eps
          exact .union_right_right h1
        | ro =>
          simp only [CapyCaptureSet.applyMut_ro, CapyCaptureSet.applyRO]
          exact .union_right_right refl'
      | var m x =>
        simp only [CapyCaptureSet.applyRO] at he
        contradiction
      | cvar m c =>
        simp only [CapyCaptureSet.applyRO] at he
        contradiction
      | pseudo_peak D =>
        simp only [CapyCaptureSet.applyRO] at he
        contradiction
  | empty =>
    contradiction
  | union_left _ h2 _ _ =>
    injection he with _ hB
    subst hB
    exact h2
  | union_right_left _ ih =>
    exact .union_right_left (ih he)
  | union_right_right _ ih =>
    exact .union_right_right (ih he)

/-- If a union is covered by `C`, so is its right component. -/
theorem union_coveredby_right {A B C : CapyCaptureSet s}
  (h : (A ∪ B).CoveredBy C) : B.CoveredBy C :=
  union_coveredby_right_aux rfl h

theorem trans {C1 C2 C3 : CapyCaptureSet s}
  (h1 : C1.CoveredBy C2) (h2 : C2.CoveredBy C3) : C1.CoveredBy C3 := by
  induction h1 generalizing C3 with
  | refl hm1 =>
    exact mut_mono_left hm1 h2
  | empty => exact empty
  | union_left _ _ ih1 ih2 =>
    exact .union_left (ih1 h2) (ih2 h2)
  | union_right_left _ ih =>
    exact ih (union_coveredby_left h2)
  | union_right_right _ ih =>
    exact ih (union_coveredby_right h2)

/-- Renaming preserves `CoveredBy`. -/
theorem rename {C1 C2 : CapyCaptureSet s1} {f : Rename s1 s2}
  (hcov : C1.CoveredBy C2) : (C1.rename f).CoveredBy (C2.rename f) := by
  induction hcov with
  | refl hm =>
    simp only [CapyCaptureSet.applyMut_rename]
    exact .refl hm
  | empty =>
    simp only [CapyCaptureSet.rename]
    exact .empty
  | union_left _ _ ih1 ih2 =>
    simp only [CapyCaptureSet.rename]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    simp only [CapyCaptureSet.rename]
    exact .union_right_left ih
  | union_right_right _ ih =>
    simp only [CapyCaptureSet.rename]
    exact .union_right_right ih

/-- applyRO preserves `CoveredBy`. -/
theorem applyRO_mono {C1 C2 : CapyCaptureSet s}
  (hcov : C1.CoveredBy C2) : C1.applyRO.CoveredBy C2.applyRO := by
  induction hcov with
  | refl hm =>
    simp only [CapyCaptureSet.applyMut_applyRO]
    exact refl'
  | empty =>
    simp only [CapyCaptureSet.applyRO]
    exact .empty
  | union_left _ _ ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO]
    exact .union_left ih1 ih2
  | union_right_left _ ih =>
    simp only [CapyCaptureSet.applyRO]
    exact .union_right_left ih
  | union_right_right _ ih =>
    simp only [CapyCaptureSet.applyRO]
    exact .union_right_right ih

/-- applyMut preserves `CoveredBy`. -/
theorem applyMut_mono {C1 C2 : CapyCaptureSet s} {m : Mutability}
  (hcov : C1.CoveredBy C2) : (C1.applyMut m).CoveredBy (C2.applyMut m) := by
  cases m with
  | epsilon => simp only [CapyCaptureSet.applyMut_epsilon]; exact hcov
  | ro => simp only [CapyCaptureSet.applyMut_ro]; exact hcov.applyRO_mono

/-- If `(.cvar a c) ⊆ D` then `(.cvar a.applyRO c) ⊆ D.applyRO`. -/
private theorem cvar_subset_applyRO {a : Access} {c : BVar s .cvar} {D : CapyCaptureSet s}
  (hsub : (.cvar a c) ⊆ D) : (.cvar a.applyRO c) ⊆ D.applyRO := by
  induction D with
  | empty => cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO]
    cases hsub with
    | union_right_left h => exact .union_right_left (ih1 h)
    | union_right_right h => exact .union_right_right (ih2 h)
  | var _ _ => cases hsub
  | cvar m' c' =>
    cases hsub
    simp only [CapyCaptureSet.applyRO]
    exact .refl
  | pseudo_peak D ih => cases hsub

/-- A cvar inside `D.applyRO` comes from an original cvar in `D`, with its mode the
    read-only image of that original mode. -/
private theorem cvar_subset_of_applyRO {a : Access} {c : BVar s .cvar} {D : CapyCaptureSet s}
  (hsub : (.cvar a c) ⊆ D.applyRO) : ∃ a0, (.cvar a0 c) ⊆ D ∧ a = a0.applyRO := by
  induction D with
  | empty =>
    simp only [CapyCaptureSet.applyRO] at hsub
    cases hsub
  | union D1 D2 ih1 ih2 =>
    simp only [CapyCaptureSet.applyRO] at hsub
    cases hsub with
    | union_right_left h =>
      obtain ⟨a0, hm, he⟩ := ih1 h
      exact ⟨a0, .union_right_left hm, he⟩
    | union_right_right h =>
      obtain ⟨a0, hm, he⟩ := ih2 h
      exact ⟨a0, .union_right_right hm, he⟩
  | var m' x =>
    simp only [CapyCaptureSet.applyRO] at hsub
    cases hsub
  | cvar m' c' =>
    simp only [CapyCaptureSet.applyRO] at hsub
    cases hsub
    exact ⟨m', .refl, rfl⟩
  | pseudo_peak D ih =>
    simp only [CapyCaptureSet.applyRO] at hsub
    cases hsub

/-- If a cvar is a subset of C1 and C1 is covered by C2, then the cvar (possibly with
    a weaker access mode) is a subset of C2. -/
theorem cvar_subset_coveredby {a : Access} {c : BVar s .cvar} {C1 C2 : CapyCaptureSet s}
  (hsub : (.cvar a c) ⊆ C1)
  (hcov : C1.CoveredBy C2) :
  ∃ a', a ≤ a' ∧ (.cvar a' c) ⊆ C2 := by
  induction hcov generalizing a with
  | refl hm =>
    rename_i D m1 m2
    cases m1 with
    | epsilon =>
      simp only [CapyCaptureSet.applyMut_epsilon] at hsub
      cases m2 with
      | epsilon =>
        simp only [CapyCaptureSet.applyMut_epsilon]
        exact ⟨a, Access.Le.refl, hsub⟩
      | ro =>
        -- impossible: .epsilon ≤ .ro does not hold
        cases hm
    | ro =>
      simp only [CapyCaptureSet.applyMut_ro] at hsub
      cases m2 with
      | epsilon =>
        simp only [CapyCaptureSet.applyMut_epsilon]
        obtain ⟨a0, h, he⟩ := cvar_subset_of_applyRO hsub
        subst he
        exact ⟨a0, Access.applyRO_le, h⟩
      | ro =>
        simp only [CapyCaptureSet.applyMut_ro]
        exact ⟨a, Access.Le.refl, hsub⟩
  | empty =>
    cases hsub
  | union_left _ _ ih1 ih2 =>
    cases hsub with
    | union_right_left hsub' => exact ih1 hsub'
    | union_right_right hsub' => exact ih2 hsub'
  | union_right_left _ ih =>
    obtain ⟨m', hle, hsub'⟩ := ih hsub
    exact ⟨m', hle, .union_right_left hsub'⟩
  | union_right_right _ ih =>
    obtain ⟨m', hle, hsub'⟩ := ih hsub
    exact ⟨m', hle, .union_right_right hsub'⟩

end CapyCaptureSet.CoveredBy

end CoreCapybara
