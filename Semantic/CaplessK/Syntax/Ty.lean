import Semantic.CaplessK.Debruijn
import Semantic.CaplessK.Syntax.CaptureSet
import Semantic.CaplessK.Syntax.Classifier

/-!
Type definitions and operations for CaplessK.
-/

namespace CaplessK

/-- The sort of a type: capturing, shape, or existential. -/
inductive TySort : Type where
/-- capturing types -/
| capt : TySort
/-- shape types -/
| shape : TySort
/-- existential types -/
| exi : TySort

/-- A capture bound, either unbound or bounded by a capture set.
  It bounds capture set parameters. -/
inductive CaptureBound : Sig -> Type where
| unbound : CapKind -> CaptureBound s
| bound : CaptureSet s -> CaptureBound s

/-- A type in CC, indexed by its sort (capturing, shape, or existential). -/
inductive Ty : TySort -> Sig -> Type where
-- shape types
| top : Ty .shape s
| tvar : BVar s .tvar -> Ty .shape s
| arrow : Ty .capt s -> Ty .exi (s,x) -> Ty .shape s
| poly : Ty .shape s -> Ty .exi (s,X) -> Ty .shape s
| cpoly : CaptureBound s -> Ty .exi (s,C) -> Ty .shape s
| unit : Ty .shape s
| bool : Ty .shape s
-- ... capability types
| cell : Ty .shape s  -- Memory cell
| cap : Ty .shape s  -- A simplistic capability
| label : Ty .shape s -> Ty .shape s  -- A boundary label
-- capturing types
| capt : CaptureSet s -> Ty .shape s -> Ty .capt s
-- existential types
| exi : Ty .capt (s,C) -> Ty .exi s
| typ : Ty .capt s -> Ty .exi s

/-- Applies a renaming to a capture bound. -/
def CaptureBound.rename : CaptureBound s1 -> Rename s1 s2 -> CaptureBound s2
| .unbound k, _ => .unbound k
| .bound cs, f => .bound (cs.rename f)

/-- Renaming by the identity renaming leaves a capture bound unchanged. -/
def CaptureBound.rename_id {cb : CaptureBound s} : cb.rename (Rename.id) = cb := by
  cases cb
  case unbound => rfl
  case bound cs => simp [CaptureBound.rename, CaptureSet.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem CaptureBound.rename_comp {cb : CaptureBound s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cb.rename f).rename g = cb.rename (f.comp g) := by
  cases cb
  case unbound => rfl
  case bound cs => simp [CaptureBound.rename, CaptureSet.rename_comp]

/-- Applies a renaming to all bound variables in a type. -/
def Ty.rename : Ty sort s1 -> Rename s1 s2 -> Ty sort s2
| .top, _ => .top
| .tvar x, f => .tvar (f.var x)
| .arrow T1 T2, f => .arrow (T1.rename f) (T2.rename (f.lift))
| .poly T1 T2, f => .poly (T1.rename f) (T2.rename (f.lift))
| .cpoly cb T, f => .cpoly (cb.rename f) (T.rename (f.lift))
| .unit, _ => .unit
| .cap, _ => .cap
| .bool, _ => .bool
| .cell, _ => .cell
| .capt cs T, f => .capt (cs.rename f) (T.rename f)
| .exi T, f => .exi (T.rename (f.lift))
| .typ T, f => .typ (T.rename f)

/-- Renaming by the identity renaming leaves a type unchanged. -/
def Ty.rename_id {T : Ty sort s} : T.rename (Rename.id) = T := by
  induction T
  case top => rfl
  case tvar => rfl
  case arrow ih1 ih2 => simp [Ty.rename, Rename.lift_id, ih1, ih2]
  case poly ih1 ih2 => simp [Ty.rename, Rename.lift_id, ih1, ih2]
  case cpoly cb ih => simp [Ty.rename, Rename.lift_id, ih, CaptureBound.rename_id]
  case unit => rfl
  case cap => rfl
  case bool => rfl
  case cell => rfl
  case capt ih2 =>
    simp [Ty.rename, ih2, CaptureSet.rename_id]
  case exi ih => simp [Ty.rename, Rename.lift_id, ih]
  case typ ih => simp [Ty.rename, ih]

/-- Renaming distributes over composition of renamings. -/
theorem Ty.rename_comp {T : Ty sort s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing s2 s3
  case top => rfl
  case tvar => rfl
  case arrow ih1 ih2 => simp [Ty.rename, Rename.lift_comp, ih1, ih2]
  case poly ih1 ih2 => simp [Ty.rename, Rename.lift_comp, ih1, ih2]
  case cpoly cb ih => simp [Ty.rename, Rename.lift_comp, ih, CaptureBound.rename_comp]
  case unit => rfl
  case cap => rfl
  case bool => rfl
  case cell => rfl
  case capt ih => simp [Ty.rename, CaptureSet.rename_comp, ih]
  case exi ih => simp [Ty.rename, Rename.lift_comp, ih]
  case typ ih => simp [Ty.rename, ih]

/-- Weakening commutes with renaming under a binder. -/
theorem Ty.weaken_rename_comm {T : Ty sort s1} {f : Rename s1 s2} :
    (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp [Ty.rename_comp, Rename.succ_lift_comm]

/-- Extracts the capture set from a capturing type. -/
def Ty.captureSet : Ty .capt s -> CaptureSet s
| .capt C _ => C

/-- A capture bound is closed if it contains no heap pointers. -/
inductive CaptureBound.IsClosed : CaptureBound s -> Prop where
| unbound : CaptureBound.IsClosed (.unbound k)
| bound : CaptureSet.IsClosed cs -> CaptureBound.IsClosed (.bound cs)

/-- A type is closed if it contains no heap pointers. -/
inductive Ty.IsClosed : Ty sort s -> Prop where
-- shape types
| top : Ty.IsClosed .top
| tvar : Ty.IsClosed (.tvar x)
| arrow : Ty.IsClosed T1 -> Ty.IsClosed T2 -> Ty.IsClosed (.arrow T1 T2)
| poly : Ty.IsClosed T1 -> Ty.IsClosed T2 -> Ty.IsClosed (.poly T1 T2)
| cpoly : CaptureBound.IsClosed cb -> Ty.IsClosed T -> Ty.IsClosed (.cpoly cb T)
| unit : Ty.IsClosed .unit
| cap : Ty.IsClosed .cap
| bool : Ty.IsClosed .bool
| cell : Ty.IsClosed .cell
-- capturing types
| capt : CaptureSet.IsClosed cs -> Ty.IsClosed S -> Ty.IsClosed (.capt cs S)
-- existential types
| exi : Ty.IsClosed T -> Ty.IsClosed (.exi T)
| typ : Ty.IsClosed T -> Ty.IsClosed (.typ T)

end CaplessK
