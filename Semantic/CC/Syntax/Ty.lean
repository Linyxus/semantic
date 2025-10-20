import Semantic.CC.Debruijn
import Semantic.CC.Syntax.CaptureSet

/-!
Type definitions and operations for CC.
-/

namespace CC

inductive TySort : Type where
-- Capturing types
| capt : TySort
-- Shape types
| shape : TySort
-- Existential types
| exi : TySort

inductive CaptureBound : Sig -> Type where
| unbound : CaptureBound s
| bound : CaptureSet s -> CaptureBound s

inductive Ty : TySort -> Sig -> Type where
-- shape types
| top : Ty .shape s
| tvar : BVar s .tvar -> Ty .shape s
| arrow : Ty .capt s -> Ty .exi (s,x) -> Ty .shape s
| poly : Ty .shape s -> Ty .exi (s,X) -> Ty .shape s
| cpoly : CaptureBound s -> Ty .exi (s,C) -> Ty .shape s
| unit : Ty .shape s
| cap : Ty .shape s
-- capturing types
| capt : CaptureSet s -> Ty .shape s -> Ty .capt s
-- existential types
| exi : Ty .capt (s,C) -> Ty .exi s
| typ : Ty .capt s -> Ty .exi s

def CaptureBound.rename : CaptureBound s1 -> Rename s1 s2 -> CaptureBound s2
| .unbound, _ => .unbound
| .bound cs, f => .bound (cs.rename f)

def CaptureBound.rename_id {cb : CaptureBound s} : cb.rename (Rename.id) = cb := by
  cases cb
  case unbound => rfl
  case bound cs => simp [CaptureBound.rename, CaptureSet.rename_id]

theorem CaptureBound.rename_comp {cb : CaptureBound s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cb.rename f).rename g = cb.rename (f.comp g) := by
  cases cb
  case unbound => rfl
  case bound cs => simp [CaptureBound.rename, CaptureSet.rename_comp]

def Ty.rename : Ty sort s1 -> Rename s1 s2 -> Ty sort s2
| .top, _ => .top
| .tvar x, f => .tvar (f.var x)
| .arrow T1 T2, f => .arrow (T1.rename f) (T2.rename (f.lift))
| .poly T1 T2, f => .poly (T1.rename f) (T2.rename (f.lift))
| .cpoly cb T, f => .cpoly (cb.rename f) (T.rename (f.lift))
| .unit, _ => .unit
| .cap, _ => .cap
| .capt cs T, f => .capt (cs.rename f) (T.rename f)
| .exi T, f => .exi (T.rename (f.lift))
| .typ T, f => .typ (T.rename f)

def Ty.rename_id {T : Ty sort s} : T.rename (Rename.id) = T := by
  induction T
  case top => rfl
  case tvar => rfl
  case arrow ih1 ih2 => simp [Ty.rename, Rename.lift_id, ih1, ih2]
  case poly ih1 ih2 => simp [Ty.rename, Rename.lift_id, ih1, ih2]
  case cpoly cb ih => simp [Ty.rename, Rename.lift_id, ih, CaptureBound.rename_id]
  case unit => rfl
  case cap => rfl
  case capt ih2 =>
    simp [Ty.rename, ih2, CaptureSet.rename_id]
  case exi ih => simp [Ty.rename, Rename.lift_id, ih]
  case typ ih => simp [Ty.rename, ih]

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
  case capt ih => simp [Ty.rename, CaptureSet.rename_comp, ih]
  case exi ih => simp [Ty.rename, Rename.lift_comp, ih]
  case typ ih => simp [Ty.rename, ih]

theorem Ty.weaken_rename_comm {T : Ty sort s1} {f : Rename s1 s2} :
    (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp [Ty.rename_comp, Rename.succ_lift_comm]

end CC
