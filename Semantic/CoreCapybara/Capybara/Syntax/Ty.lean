import Semantic.CoreCapybara.Debruijn
import Semantic.CoreCapybara.Syntax.CaptureSet
import Semantic.CoreCapybara.Capybara.Syntax.CaptureSet
import Semantic.CoreCapybara.Syntax.SepCtx

/-!
Type definitions and operations for CC.
-/

namespace CoreCapybara

/-- A capture bound, either unbound or bounded by a capture set. -/
inductive CapyCaptureBound : Sig -> Type where
| unbound : Mutability -> CapyCaptureBound s
| bound : CapyCaptureSet s -> CapyCaptureBound s

/-- Applies a renaming to a capture bound. -/
def CapyCaptureBound.rename : CapyCaptureBound s1 -> Rename s1 s2 -> CapyCaptureBound s2
| .unbound m, _ => .unbound m
| .bound cs, f => .bound (cs.rename f)

/-- Renaming by the identity renaming leaves a capture bound unchanged. -/
def CapyCaptureBound.rename_id {cb : CapyCaptureBound s} : cb.rename (Rename.id) = cb := by
  cases cb with
  | unbound m => rfl
  | bound cs => simp [CapyCaptureBound.rename, CapyCaptureSet.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem CapyCaptureBound.rename_comp
    {cb : CapyCaptureBound s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cb.rename f).rename g = cb.rename (f.comp g) := by
  cases cb with
  | unbound m => rfl
  | bound cs => simp [CapyCaptureBound.rename, CapyCaptureSet.rename_comp]

/-- Sort of a Capybara type. -/
inductive CapyTySort : Type where
-- Capturing types
| capt
-- Existential types
| exi

/-- A type in CC, indexed by its sort (capturing or existential). -/
inductive CapyTy : CapyTySort -> Sig -> Type where
-- capturing types
| top : CapyTy .capt s
| tvar : BVar s .tvar -> CapyTy .capt s
| arrow :
  CapyTy .capt (s,C) ->  -- a capture parameter is implicitly bound
  CapyCaptureSet s ->
  CapyTy .exi (s,x) ->
  CapyTy .capt s
| poly :
  CapyTy .capt s ->
  CapyCaptureSet s ->
  CapyTy .exi (s,X) ->
  CapyTy .capt s
| cpoly :
  CapyCaptureBound s ->
  CapyCaptureSet s ->
  CapyTy .exi (s,C) ->
  CapyTy .capt s
| cap : CapyCaptureSet s -> CapyTy .capt s
| cell : CapyCaptureSet s -> Mutability -> CapyTy .capt s
-- Reader is obsolete, since cell additionally has `Mutability`
| unit : CapyTy .capt s
| bool : CapyTy .capt s
-- existential types
| exi : CapyTy .capt (s,C) -> CapyTy .exi s
| typ : CapyTy .capt s -> CapyTy .exi s

/-- Applies a renaming to all bound variables in a type. -/
def CapyTy.rename : CapyTy sort s1 -> Rename s1 s2 -> CapyTy sort s2
| .top, _ => .top
| .tvar x, f => .tvar (f.var x)
| .arrow T1 cs T2, f => .arrow (T1.rename (f.lift)) (cs.rename f) (T2.rename (f.lift))
| .poly T1 cs T2, f => .poly (T1.rename f) (cs.rename f) (T2.rename (f.lift))
| .cpoly cb cs T, f => .cpoly (cb.rename f) (cs.rename f) (T.rename (f.lift))
| .unit, _ => .unit
| .cap cs, f => .cap (cs.rename f)
| .bool, _ => .bool
| .cell cs m, f => .cell (cs.rename f) m
| .exi T, f => .exi (T.rename (f.lift))
| .typ T, f => .typ (T.rename f)

/-- Renaming by the identity renaming leaves a type unchanged. -/
def CapyTy.rename_id {T : CapyTy sort s} : T.rename (Rename.id) = T := by
  induction T with
  | top => simp only [CapyTy.rename]
  | tvar x => simp only [CapyTy.rename, Rename.id]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.rename, Rename.lift_id, CapyCaptureSet.rename_id]
    congr 1
  | poly T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.rename, Rename.lift_id, CapyCaptureSet.rename_id, ih1]
    exact congrArg (CapyTy.poly T1 cs) ih2
  | cpoly cb cs T ih =>
    simp only [CapyTy.rename, Rename.lift_id, CapyCaptureBound.rename_id, CapyCaptureSet.rename_id]
    exact congrArg (CapyTy.cpoly cb cs) ih
  | cap cs => simp only [CapyTy.rename, CapyCaptureSet.rename_id]
  | cell cs m => simp only [CapyTy.rename, CapyCaptureSet.rename_id]
  | unit => simp only [CapyTy.rename]
  | bool => simp only [CapyTy.rename]
  | exi T ih =>
    simp only [CapyTy.rename, Rename.lift_id]
    exact congrArg CapyTy.exi ih
  | typ T ih =>
    simp only [CapyTy.rename]
    exact congrArg CapyTy.typ ih

/-- Renaming distributes over composition of renamings. -/
theorem CapyTy.rename_comp {T : CapyTy sort s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing s2 s3 with
  | top => simp only [CapyTy.rename]
  | tvar x => simp only [CapyTy.rename, Rename.comp]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [CapyTy.rename, CapyCaptureSet.rename_comp, Rename.lift_comp]
    congr 1
    · exact ih1 (f := f.lift) (g := g.lift)
    · exact ih2 (f := f.lift) (g := g.lift)
  | poly T1 cs T2 ih1 ih2 =>
    simpa only [CapyTy.rename, CapyCaptureSet.rename_comp, Rename.lift_comp, ih1] using
      congrArg (CapyTy.poly (T1.rename (f.comp g)) (cs.rename (f.comp g)))
        (ih2 (f := f.lift) (g := g.lift))
  | cpoly cb cs T ih =>
    simpa only [
      CapyTy.rename, CapyCaptureBound.rename_comp, CapyCaptureSet.rename_comp, Rename.lift_comp
    ] using
      congrArg (CapyTy.cpoly (cb.rename (f.comp g)) (cs.rename (f.comp g)))
        (ih (f := f.lift) (g := g.lift))
  | cap cs => simp only [CapyTy.rename, CapyCaptureSet.rename_comp]
  | cell cs m => simp only [CapyTy.rename, CapyCaptureSet.rename_comp]
  | unit => simp only [CapyTy.rename]
  | bool => simp only [CapyTy.rename]
  | exi T ih =>
    simpa only [CapyTy.rename, Rename.lift_comp] using
      congrArg CapyTy.exi (ih (f := f.lift) (g := g.lift))
  | typ T ih =>
    simpa only [CapyTy.rename] using congrArg CapyTy.typ (ih (f := f) (g := g))

/-- Weakening commutes with renaming under a binder. -/
theorem CapyTy.weaken_rename_comm {T : CapyTy sort s1} {f : Rename s1 s2} :
    (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp [CapyTy.rename_comp, Rename.succ_lift_comm]

/-- Extracts the capture set from a capturing type. -/
def CapyTy.captureSet : CapyTy .capt s -> CapyCaptureSet s
| .top => .empty
| .tvar _ => .empty
| .arrow _ cs _ => cs
| .poly _ cs _ => cs
| .cpoly _ cs _ => cs
| .cap cs => cs
| .cell cs _ => cs
| .unit => .empty
| .bool => .empty

def CapyTy.refineCaptureSet : CapyTy .capt s -> CapyCaptureSet s -> CapyTy .capt s
| .top, _ => .top
| .tvar x, _ => .tvar x
| .arrow T1 _ T2, cs => .arrow T1 cs T2
| .poly T1 _ T2, cs => .poly T1 cs T2
| .cpoly cb _ T, cs => .cpoly cb cs T
| .cap _, cs => .cap cs
| .cell _ m, cs => .cell cs m
| .unit, _ => .unit
| .bool, _ => .bool

/-- A capture bound is closed if it contains no heap pointers. -/
inductive CapyCaptureBound.IsClosed : CapyCaptureBound s -> Prop where
| unbound : CapyCaptureBound.IsClosed (.unbound m)
| bound : CapyCaptureSet.IsClosed cs -> CapyCaptureBound.IsClosed (.bound cs)

/-- A type is closed if it contains no heap pointers. -/
inductive CapyTy.IsClosed : CapyTy sort s -> Prop where
| top : CapyTy.IsClosed .top
| tvar : CapyTy.IsClosed (.tvar x)
| arrow : CapyTy.IsClosed T1 -> CapyCaptureSet.IsClosed cs -> CapyTy.IsClosed T2 ->
    CapyTy.IsClosed (.arrow T1 cs T2)
| poly : CapyTy.IsClosed T1 -> CapyCaptureSet.IsClosed cs -> CapyTy.IsClosed T2 ->
    CapyTy.IsClosed (.poly T1 cs T2)
| cpoly :
    CapyCaptureBound.IsClosed cb -> CapyCaptureSet.IsClosed cs -> CapyTy.IsClosed T ->
    CapyTy.IsClosed (.cpoly cb cs T)
| unit : CapyTy.IsClosed .unit
| cap : CapyCaptureSet.IsClosed cs -> CapyTy.IsClosed (.cap cs)
| bool : CapyTy.IsClosed .bool
| cell : CapyCaptureSet.IsClosed cs -> CapyTy.IsClosed (.cell cs m)
| exi : CapyTy.IsClosed T -> CapyTy.IsClosed (.exi T)
| typ : CapyTy.IsClosed T -> CapyTy.IsClosed (.typ T)

/-- The capture set of a renamed type equals the renamed capture set. -/
theorem CapyTy.captureSet_rename {T : CapyTy .capt s1} {f : Rename s1 s2} :
    (T.rename f).captureSet = T.captureSet.rename f := by
  cases T <;> simp [CapyTy.rename, CapyTy.captureSet, CapyCaptureSet.rename]

/-- The predicate that a capturing type is pure. -/
def CapyTy.IsPureType (T : CapyTy .capt s) : Prop :=
  T.captureSet.IsEmpty

/-- Renaming preserves purity. -/
theorem CapyTy.IsPureType.rename {T : CapyTy .capt s1} (h : T.IsPureType) (f : Rename s1 s2) :
    (T.rename f).IsPureType := by
  unfold IsPureType at *
  rw [CapyTy.captureSet_rename]
  exact h.rename f

/-- A pure capturing type. -/
structure CapyPureTy (s : Sig) where
  core : CapyTy .capt s
  p : CapyTy.IsPureType core

/-- Creates a pure type from a type variable. Type variables have empty capture sets. -/
def CapyPureTy.tvar (x : BVar s .tvar) : CapyPureTy s :=
  ⟨.tvar x, CapyCaptureSet.IsEmpty.empty⟩

/-- Top type is pure. -/
def CapyPureTy.top : CapyPureTy s :=
  ⟨.top, CapyCaptureSet.IsEmpty.empty⟩

/-- Unit type is pure. -/
def CapyPureTy.unit : CapyPureTy s :=
  ⟨.unit, CapyCaptureSet.IsEmpty.empty⟩

/-- Bool type is pure. -/
def CapyPureTy.bool : CapyPureTy s :=
  ⟨.bool, CapyCaptureSet.IsEmpty.empty⟩

/-- Renames a pure type. -/
def CapyPureTy.rename (T : CapyPureTy s1) (f : Rename s1 s2) : CapyPureTy s2 :=
  ⟨T.core.rename f, T.p.rename f⟩

/-- Renaming by the identity renaming leaves a pure type unchanged. -/
theorem CapyPureTy.rename_id {T : CapyPureTy s} : T.rename Rename.id = T := by
  simp only [CapyPureTy.rename, CapyTy.rename_id]

/-- Renaming distributes over composition of renamings for pure types. -/
theorem CapyPureTy.rename_comp {T : CapyPureTy s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  simp only [CapyPureTy.rename, CapyTy.rename_comp]

/-- A pure type is closed if its core is closed. -/
def CapyPureTy.IsClosed (T : CapyPureTy s) : Prop :=
  T.core.IsClosed

end CoreCapybara
