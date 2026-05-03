import Semantic.Consume.Syntax
import Semantic.Consume.Substitution

namespace Consume

/-- A peak is consumable if it is accessed at `consume` mode, and it is not locked. -/
inductive ConsumablePeak : Ctx s -> BVar s .cvar -> Prop where
| lookup {Γ : Ctx s} :
  Γ.LookupCVar c UseMode.consume B false ->
  -------------------
  ConsumablePeak Γ c

/-- A capture set is consumable if all its peaks are consumable. -/
def CaptureSet.consumable (Γ : Ctx s) (C : CaptureSet s) : Prop :=
  ∀ m c, (CaptureSet.cvar m c) ⊆ C.peaks Γ -> ConsumablePeak Γ c

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
| lock {Γ1 Γ2 Γ3 : Ctx s} :
  SeqComp Γ1 Γ2 Γ3 ->
  -------------------
  SeqComp Γ1.lock Γ2.lock Γ3.lock

end Consume
