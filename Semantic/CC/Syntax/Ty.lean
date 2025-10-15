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

inductive Ty : TySort -> Sig -> Type where
| top : Ty .shape s
| tvar : BVar s .tvar -> Ty .shape s
| arrow : Ty .shape s -> Ty .shape (s,x) -> Ty .shape s
| poly : Ty .shape s -> Ty .shape (s,X) -> Ty .shape s

def Ty.rename : Ty sort s1 -> Rename s1 s2 -> Ty sort s2
| .top, _ => .top
| .tvar x, f => .tvar (f.var x)
| .arrow T1 T2, f => .arrow (T1.rename f) (T2.rename (f.lift))
| .poly T1 T2, f => .poly (T1.rename f) (T2.rename (f.lift))

def Ty.rename_id {T : Ty sort s} : T.rename (Rename.id) = T := by
  induction T
  case top => rfl
  case tvar => rfl
  case arrow ih1 ih2 => simp [Ty.rename, Rename.lift_id, ih1, ih2]
  case poly ih1 ih2 => simp [Ty.rename, Rename.lift_id, ih1, ih2]

theorem Ty.rename_comp {T : Ty sort s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing s2 s3
  case top => rfl
  case tvar => rfl
  case arrow ih1 ih2 => simp [Ty.rename, Rename.lift_comp, ih1, ih2]
  case poly ih1 ih2 => simp [Ty.rename, Rename.lift_comp, ih1, ih2]

theorem Ty.weaken_rename_comm {T : Ty sort s1} {f : Rename s1 s2} :
    (T.rename Rename.succ).rename (f.lift (k:=k0)) = (T.rename f).rename (Rename.succ) := by
  simp [Ty.rename_comp, Rename.succ_lift_comm]

end CC
