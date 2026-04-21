import Semantic.ModalCapybara.Debruijn
import Semantic.ModalCapybara.Syntax.CaptureSet
import Semantic.ModalCapybara.Syntax.SepCtx

/-!
Type definitions and operations for CC.
-/

namespace ModalCapybara

/-- The sort of a type: capturing, shape, or existential. -/
inductive TySort : Type where
/-- capturing types -/
| capt : TySort
/-- existential types -/
| exi : TySort

/-- A capture bound, either unbound or bounded by a capture set. -/
inductive CaptureBound : Sig -> Type where
| unbound : CaptureBound s
| bound : CaptureSet s -> CaptureBound s

/-- Applies a renaming to a capture bound. -/
def CaptureBound.rename : CaptureBound s1 -> Rename s1 s2 -> CaptureBound s2
| .unbound, _ => .unbound
| .bound cs, f => .bound (cs.rename f)

/-- Renaming by the identity renaming leaves a capture bound unchanged. -/
def CaptureBound.rename_id {cb : CaptureBound s} : cb.rename (Rename.id) = cb := by
  cases cb with
  | unbound => rfl
  | bound cs => simp [CaptureBound.rename, CaptureSet.rename_id]

/-- Renaming distributes over composition of renamings. -/
theorem CaptureBound.rename_comp
    {cb : CaptureBound s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (cb.rename f).rename g = cb.rename (f.comp g) := by
  cases cb with
  | unbound => rfl
  | bound cs => simp [CaptureBound.rename, CaptureSet.rename_comp]

/-- A type in CC, indexed by its sort (capturing, shape, or existential). -/
inductive Ty : TySort -> Sig -> Type where
-- capturing types
| top : Ty .capt s
| tvar : BVar s .tvar -> Ty .capt s
| arrow : Ty .capt s -> CaptureSet s -> Ty .exi (s,x) -> Ty .capt s
| poly : Ty .capt s -> CaptureSet s -> Ty .exi (s,X) -> Ty .capt s
| cpoly : CaptureBound s -> CaptureSet s -> Ty .exi (s,C) -> Ty .capt s
| modal : CaptureSet s -> SepCtx s -> Ty .exi s -> Ty .capt s
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
| .cpoly cb cs T, f => .cpoly (cb.rename f) (cs.rename f) (T.rename (f.lift))
| .modal cs Ψ T, f => .modal (cs.rename f) (Ψ.rename f) (T.rename f)
| .unit, _ => .unit
| .cap cs, f => .cap (cs.rename f)
| .bool, _ => .bool
| .cell cs, f => .cell (cs.rename f)
| .reader cs, f => .reader (cs.rename f)
| .exi T, f => .exi (T.rename (f.lift))
| .typ T, f => .typ (T.rename f)

/-- Renaming by the identity renaming leaves a type unchanged. -/
def Ty.rename_id {T : Ty sort s} : T.rename (Rename.id) = T := by
  induction T with
  | top => rfl
  | tvar x =>
    simp only [Ty.rename, Rename.id]
  | arrow T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename, Rename.lift_id, CaptureSet.rename_id, ih1]
    exact congrArg (Ty.arrow T1 cs) ih2
  | poly T1 cs T2 ih1 ih2 =>
    simp only [Ty.rename, Rename.lift_id, CaptureSet.rename_id, ih1]
    exact congrArg (Ty.poly T1 cs) ih2
  | cpoly cb cs T ih =>
    simp only [Ty.rename, Rename.lift_id, CaptureBound.rename_id, CaptureSet.rename_id]
    exact congrArg (Ty.cpoly cb cs) ih
  | modal cs Ψ T ih =>
    simp only [Ty.rename, CaptureSet.rename_id, SepCtx.rename_id]
    exact congrArg (Ty.modal cs Ψ) ih
  | cap cs =>
    simp only [Ty.rename, CaptureSet.rename_id]
  | cell cs =>
    simp only [Ty.rename, CaptureSet.rename_id]
  | reader cs =>
    simp only [Ty.rename, CaptureSet.rename_id]
  | unit => rfl
  | bool => rfl
  | exi T ih =>
    simp only [Ty.rename, Rename.lift_id]
    exact congrArg Ty.exi ih
  | typ T ih =>
    simp only [Ty.rename]
    exact congrArg Ty.typ ih

/-- Renaming distributes over composition of renamings. -/
theorem Ty.rename_comp {T : Ty sort s1} {f : Rename s1 s2} {g : Rename s2 s3} :
    (T.rename f).rename g = T.rename (f.comp g) := by
  induction T generalizing s2 s3 with
  | top => rfl
  | tvar x =>
    simp only [Ty.rename, Rename.comp]
  | arrow T1 cs T2 ih1 ih2 =>
    simpa only [Ty.rename, CaptureSet.rename_comp, Rename.lift_comp, ih1] using
      congrArg (Ty.arrow (T1.rename (f.comp g)) (cs.rename (f.comp g)))
        (ih2 (f := f.lift) (g := g.lift))
  | poly T1 cs T2 ih1 ih2 =>
    simpa only [Ty.rename, CaptureSet.rename_comp, Rename.lift_comp, ih1] using
      congrArg (Ty.poly (T1.rename (f.comp g)) (cs.rename (f.comp g)))
        (ih2 (f := f.lift) (g := g.lift))
  | cpoly cb cs T ih =>
    simpa only [Ty.rename, CaptureBound.rename_comp, CaptureSet.rename_comp, Rename.lift_comp] using
      congrArg (Ty.cpoly (cb.rename (f.comp g)) (cs.rename (f.comp g)))
        (ih (f := f.lift) (g := g.lift))
  | modal cs Ψ T ih =>
    simpa only [Ty.rename, CaptureSet.rename_comp, SepCtx.rename_comp] using
      congrArg (Ty.modal (cs.rename (f.comp g)) (Ψ.rename (f.comp g))) (ih (f := f) (g := g))
  | cap cs =>
    simp only [Ty.rename, CaptureSet.rename_comp]
  | cell cs =>
    simp only [Ty.rename, CaptureSet.rename_comp]
  | reader cs =>
    simp only [Ty.rename, CaptureSet.rename_comp]
  | unit => rfl
  | bool => rfl
  | exi T ih =>
    simpa only [Ty.rename, Rename.lift_comp] using
      congrArg Ty.exi (ih (f := f.lift) (g := g.lift))
  | typ T ih =>
    simpa only [Ty.rename] using congrArg Ty.typ (ih (f := f) (g := g))

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
| .modal cs _ _ => cs
| .cap cs => cs
| .cell cs => cs
| .reader cs => cs
| .unit => .empty
| .bool => .empty

def Ty.refineCaptureSet : Ty .capt s -> CaptureSet s -> Ty .capt s
| .top, _ => .top
| .tvar x, _ => .tvar x
| .arrow T1 _ T2, cs => .arrow T1 cs T2
| .poly T1 _ T2, cs => .poly T1 cs T2
| .cpoly cb _ T, cs => .cpoly cb cs T
| .modal _ Ψ T, cs => .modal cs Ψ T
| .cap _, cs => .cap cs
| .cell _, cs => .cell cs
| .reader _, cs => .reader cs
| .unit, _ => .unit
| .bool, _ => .bool

/-- A capture bound is closed if it contains no heap pointers. -/
inductive CaptureBound.IsClosed : CaptureBound s -> Prop where
| unbound : CaptureBound.IsClosed .unbound
| bound : CaptureSet.IsClosed cs -> CaptureBound.IsClosed (.bound cs)

/-- A type is closed if it contains no heap pointers. -/
inductive Ty.IsClosed : Ty sort s -> Prop where
| top : Ty.IsClosed .top
| tvar : Ty.IsClosed (.tvar x)
| arrow : Ty.IsClosed T1 -> CaptureSet.IsClosed cs -> Ty.IsClosed T2 ->
    Ty.IsClosed (.arrow T1 cs T2)
| poly : Ty.IsClosed T1 -> CaptureSet.IsClosed cs -> Ty.IsClosed T2 ->
    Ty.IsClosed (.poly T1 cs T2)
| cpoly :
    CaptureBound.IsClosed cb -> CaptureSet.IsClosed cs -> Ty.IsClosed T ->
    Ty.IsClosed (.cpoly cb cs T)
| modal :
    CaptureSet.IsClosed cs -> SepCtx.IsClosed Ψ -> Ty.IsClosed T ->
    Ty.IsClosed (.modal cs Ψ T)
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

end ModalCapybara
