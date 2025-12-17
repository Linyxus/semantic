import Semantic.Capybara.Debruijn
import Semantic.Capybara.Syntax.CaptureSet

/-!
Type definitions and operations for CC.
-/

namespace Capybara

/-- The sort of a type: capturing, shape, or existential. -/
inductive TySort : Type where
/-- capturing types -/
| capt : TySort
/-- existential types -/
| exi : TySort

/-- A type in CC, indexed by its sort (capturing, shape, or existential). -/
inductive Ty : TySort -> Sig -> Type where
-- shape types
| top : Ty .capt s
| tvar : BVar s .tvar -> Ty .capt s
| arrow : Ty .capt s -> CaptureSet s -> Ty .exi (s,x) -> Ty .capt s
| poly : Ty .capt s -> CaptureSet s -> Ty .exi (s,X) -> Ty .capt s
| cpoly : Mutability -> CaptureSet s -> Ty .exi (s,C) -> Ty .capt s
| cap : CaptureSet s -> Ty .capt s
| cell : CaptureSet s -> Ty .capt s
| reader : CaptureSet s -> Ty .capt s
| unit : Ty .capt s
| bool : Ty .capt s
-- existential types
| exi : Ty .capt (s,C) -> Ty .exi s
| typ : Ty .capt s -> Ty .exi s

/-- Applies a renaming to all bound variables in a type. -/
def Ty.rename : Ty sort s1 -> Rename s1 s2 -> Ty sort s2
| .top, _ => .top
| .tvar x, f => .tvar (f.var x)
| .arrow T1 cs T2, f => .arrow (T1.rename f) (cs.rename f) (T2.rename (f.lift))
| .poly T1 cs T2, f => .poly (T1.rename f) (cs.rename f) (T2.rename (f.lift))
| .cpoly m cs T, f => .cpoly m (cs.rename f) (T.rename (f.lift))
| .unit, _ => .unit
| .cap cs, f => .cap (cs.rename f)
| .bool, _ => .bool
| .cell cs, f => .cell (cs.rename f)
| .reader cs, f => .reader (cs.rename f)
| .exi T, f => .exi (T.rename (f.lift))
| .typ T, f => .typ (T.rename f)

/-- Renaming by the identity renaming leaves a type unchanged. -/
def Ty.rename_id {T : Ty sort s} : T.rename (Rename.id) = T := by
  induction T
  case top => rfl
  case tvar => rfl
  case arrow ih1 ih2 => simp [Ty.rename, Rename.lift_id, CaptureSet.rename_id, ih1, ih2]
  case poly ih1 ih2 => simp [Ty.rename, Rename.lift_id, CaptureSet.rename_id, ih1, ih2]
  case cpoly ih => simp [Ty.rename, Rename.lift_id, CaptureSet.rename_id, ih]
  case unit => rfl
  case cap => simp [Ty.rename, CaptureSet.rename_id]
  case bool => rfl
  case cell => simp [Ty.rename, CaptureSet.rename_id]
  case reader => simp [Ty.rename, CaptureSet.rename_id]
  case exi ih => simp [Ty.rename, Rename.lift_id, ih]
  case typ ih => simp [Ty.rename, ih]

/-- Renaming distributes over composition of renamings. -/
theorem Ty.rename_comp {T : Ty sort s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing s2 s3
  case top => rfl
  case tvar => rfl
  case arrow ih1 ih2 => simp [Ty.rename, Rename.lift_comp, CaptureSet.rename_comp, ih1, ih2]
  case poly ih1 ih2 => simp [Ty.rename, Rename.lift_comp, CaptureSet.rename_comp, ih1, ih2]
  case cpoly ih => simp [Ty.rename, Rename.lift_comp, CaptureSet.rename_comp, ih]
  case unit => rfl
  case cap => simp [Ty.rename, CaptureSet.rename_comp]
  case bool => rfl
  case cell => simp [Ty.rename, CaptureSet.rename_comp]
  case reader => simp [Ty.rename, CaptureSet.rename_comp]
  case exi ih => simp [Ty.rename, Rename.lift_comp, ih]
  case typ ih => simp [Ty.rename, ih]

/-- Weakening commutes with renaming under a binder. -/
theorem Ty.weaken_rename_comm {T : Ty sort s1} {f : Rename s1 s2} :
    (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp [Ty.rename_comp, Rename.succ_lift_comm]

/-- Extracts the capture set from a capturing type. -/
def Ty.captureSet : Ty .capt s -> CaptureSet s
| .top => .empty
| .tvar _ => .empty
| .arrow _ cs _ => cs
| .poly _ cs _ => cs
| .cpoly _ cs _ => cs
| .cap cs => cs
| .cell cs => cs
| .reader cs => cs
| .unit => .empty
| .bool => .empty

/-- A type is closed if it contains no heap pointers. -/
inductive Ty.IsClosed : Ty sort s -> Prop where
| top : Ty.IsClosed .top
| tvar : Ty.IsClosed (.tvar x)
| arrow : Ty.IsClosed T1 -> CaptureSet.IsClosed cs -> Ty.IsClosed T2 ->
    Ty.IsClosed (.arrow T1 cs T2)
| poly : Ty.IsClosed T1 -> CaptureSet.IsClosed cs -> Ty.IsClosed T2 ->
    Ty.IsClosed (.poly T1 cs T2)
| cpoly : CaptureSet.IsClosed cs -> Ty.IsClosed T -> Ty.IsClosed (.cpoly m cs T)
| unit : Ty.IsClosed .unit
| cap : CaptureSet.IsClosed cs -> Ty.IsClosed (.cap cs)
| bool : Ty.IsClosed .bool
| cell : CaptureSet.IsClosed cs -> Ty.IsClosed (.cell cs)
| reader : CaptureSet.IsClosed cs -> Ty.IsClosed (.reader cs)
| exi : Ty.IsClosed T -> Ty.IsClosed (.exi T)
| typ : Ty.IsClosed T -> Ty.IsClosed (.typ T)

/-- The capture set of a renamed type equals the renamed capture set. -/
theorem Ty.captureSet_rename {T : Ty .capt s1} {f : Rename s1 s2} :
    (T.rename f).captureSet = T.captureSet.rename f := by
  cases T <;> simp [Ty.rename, Ty.captureSet, CaptureSet.rename]

/-- The predicate that a capturing type is pure. -/
def Ty.IsPureType (T : Ty .capt s) : Prop :=
  T.captureSet.IsEmpty

/-- Renaming preserves purity. -/
theorem Ty.IsPureType.rename {T : Ty .capt s1} (h : T.IsPureType) (f : Rename s1 s2) :
    (T.rename f).IsPureType := by
  unfold IsPureType at *
  rw [Ty.captureSet_rename]
  exact h.rename f

/-- A pure capturing type. -/
structure PureTy (s : Sig) where
  core : Ty .capt s
  p : Ty.IsPureType core

/-- Creates a pure type from a type variable. Type variables have empty capture sets. -/
def PureTy.tvar (x : BVar s .tvar) : PureTy s :=
  ⟨.tvar x, CaptureSet.IsEmpty.empty⟩

/-- Top type is pure. -/
def PureTy.top : PureTy s :=
  ⟨.top, CaptureSet.IsEmpty.empty⟩

/-- Unit type is pure. -/
def PureTy.unit : PureTy s :=
  ⟨.unit, CaptureSet.IsEmpty.empty⟩

/-- Bool type is pure. -/
def PureTy.bool : PureTy s :=
  ⟨.bool, CaptureSet.IsEmpty.empty⟩

/-- Renames a pure type. -/
def PureTy.rename (T : PureTy s1) (f : Rename s1 s2) : PureTy s2 :=
  ⟨T.core.rename f, T.p.rename f⟩

/-- Renaming by the identity renaming leaves a pure type unchanged. -/
theorem PureTy.rename_id {T : PureTy s} : T.rename Rename.id = T := by
  simp only [PureTy.rename, Ty.rename_id]

/-- Renaming distributes over composition of renamings for pure types. -/
theorem PureTy.rename_comp {T : PureTy s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  simp only [PureTy.rename, Ty.rename_comp]

/-- A pure type is closed if its core is closed. -/
def PureTy.IsClosed (T : PureTy s) : Prop :=
  T.core.IsClosed

end Capybara
