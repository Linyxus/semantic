import Semantic.Consume.Syntax
import Semantic.Consume.Substitution
import Semantic.Consume.TypeSystem.BasicProps

namespace Consume

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

/-- Sequential composition of use modes is functional in the result. -/
theorem UseMode.SeqComp.det
  {m1 m2 m3 m3' : UseMode}
  (h1 : UseMode.SeqComp m1 m2 m3)
  (h2 : UseMode.SeqComp m1 m2 m3') : m3 = m3' := by
  cases h1 <;> cases h2 <;> rfl

/-- `.empty` is the left identity of sequential composition. -/
theorem UseMode.SeqComp.left_id {m : UseMode} : UseMode.SeqComp .empty m m :=
  .l_empty

/-- `.empty` is the right identity of sequential composition. -/
theorem UseMode.SeqComp.right_id {m : UseMode} : UseMode.SeqComp m .empty m :=
  .r_empty

/-- Sequential composition of contexts is functional in the result. -/
theorem Ctx.SeqComp.det
  {Γ1 Γ2 Γ3 Γ3' : Ctx s}
  (h1 : Ctx.SeqComp Γ1 Γ2 Γ3)
  (h2 : Ctx.SeqComp Γ1 Γ2 Γ3') : Γ3 = Γ3' := by
  induction h1 with
  | empty => cases h2; rfl
  | push_var _ ih =>
    cases h2 with
    | push_var h2' => rw [ih h2']
  | push_tvar _ ih =>
    cases h2 with
    | push_tvar h2' => rw [ih h2']
  | push_cvar _ hm ih =>
    cases h2 with
    | push_cvar h2' hm' =>
      rw [ih h2', UseMode.SeqComp.det hm hm']
  | lock _ ih =>
    cases h2 with
    | lock h2' => rw [ih h2']

/-- `LookupVar` is preserved by `Ctx.SeqComp` from `Γ1` to `Γ3`. Term variable
bindings are identical across all three contexts, so the lookup is unaffected. -/
theorem Ctx.SeqComp.lookup_var_left
  {Γ1 Γ2 Γ3 : Ctx s} {x : BVar s .var} {T : Ty .capt s}
  (h : Ctx.SeqComp Γ1 Γ2 Γ3) (hx : Γ1.LookupVar x T) : Γ3.LookupVar x T := by
  induction h with
  | empty => exact hx
  | push_var _ ih =>
    cases hx with
    | here => exact .here
    | there hx' => exact .there (ih hx')
  | push_tvar _ ih =>
    cases hx with
    | there hx' => exact .there (ih hx')
  | push_cvar _ _ ih =>
    cases hx with
    | there hx' => exact .there (ih hx')
  | lock _ ih =>
    cases hx with
    | lock hx' => exact .lock (ih hx')

/-- `LookupVar` is preserved by `Ctx.SeqComp` from `Γ3` to `Γ1`. -/
theorem Ctx.SeqComp.lookup_var_right
  {Γ1 Γ2 Γ3 : Ctx s} {x : BVar s .var} {T : Ty .capt s}
  (h : Ctx.SeqComp Γ1 Γ2 Γ3) (hx : Γ3.LookupVar x T) : Γ1.LookupVar x T := by
  induction h with
  | empty => exact hx
  | push_var _ ih =>
    cases hx with
    | here => exact .here
    | there hx' => exact .there (ih hx')
  | push_tvar _ ih =>
    cases hx with
    | there hx' => exact .there (ih hx')
  | push_cvar _ _ ih =>
    cases hx with
    | there hx' => exact .there (ih hx')
  | lock _ ih =>
    cases hx with
    | lock hx' => exact .lock (ih hx')

/-- `LookupTVar` is preserved by `Ctx.SeqComp` from `Γ1` to `Γ3`. -/
theorem Ctx.SeqComp.lookup_tvar_left
  {Γ1 Γ2 Γ3 : Ctx s} {X : BVar s .tvar} {S : PureTy s}
  (h : Ctx.SeqComp Γ1 Γ2 Γ3) (hx : Γ1.LookupTVar X S) : Γ3.LookupTVar X S := by
  induction h with
  | empty => exact hx
  | push_var _ ih =>
    cases hx with
    | there hx' => exact .there (ih hx')
  | push_tvar _ ih =>
    cases hx with
    | here => exact .here
    | there hx' => exact .there (ih hx')
  | push_cvar _ _ ih =>
    cases hx with
    | there hx' => exact .there (ih hx')
  | lock _ ih =>
    cases hx with
    | lock hx' => exact .lock (ih hx')

/-- `LookupTVar` is preserved by `Ctx.SeqComp` from `Γ3` to `Γ1`. -/
theorem Ctx.SeqComp.lookup_tvar_right
  {Γ1 Γ2 Γ3 : Ctx s} {X : BVar s .tvar} {S : PureTy s}
  (h : Ctx.SeqComp Γ1 Γ2 Γ3) (hx : Γ3.LookupTVar X S) : Γ1.LookupTVar X S := by
  induction h with
  | empty => exact hx
  | push_var _ ih =>
    cases hx with
    | there hx' => exact .there (ih hx')
  | push_tvar _ ih =>
    cases hx with
    | here => exact .here
    | there hx' => exact .there (ih hx')
  | push_cvar _ _ ih =>
    cases hx with
    | there hx' => exact .there (ih hx')
  | lock _ ih =>
    cases hx with
    | lock hx' => exact .lock (ih hx')

/-- A cvar lookup in the composed context `Γ3` decomposes into corresponding
lookups in `Γ1` and `Γ2`, with use modes related by `UseMode.SeqComp`. The
capture bound and lock-flag are shared (since both contexts have the same
shape). -/
theorem Ctx.SeqComp.lookup_cvar_split
  {Γ1 Γ2 Γ3 : Ctx s} {c : BVar s .cvar} {m3 : UseMode}
  {cb : CaptureBound s} {locked : Bool}
  (h : Ctx.SeqComp Γ1 Γ2 Γ3)
  (hc : Γ3.LookupCVar c m3 cb locked) :
  ∃ m1 m2,
    Γ1.LookupCVar c m1 cb locked ∧
    Γ2.LookupCVar c m2 cb locked ∧
    UseMode.SeqComp m1 m2 m3 := by
  induction h generalizing m3 locked with
  | empty => cases hc
  | push_var _ ih =>
    cases hc with
    | there hc' =>
      obtain ⟨m1, m2, h1, h2, hm⟩ := ih hc'
      exact ⟨m1, m2, .there h1, .there h2, hm⟩
  | push_tvar _ ih =>
    cases hc with
    | there hc' =>
      obtain ⟨m1, m2, h1, h2, hm⟩ := ih hc'
      exact ⟨m1, m2, .there h1, .there h2, hm⟩
  | push_cvar _ hm ih =>
    cases hc with
    | here => exact ⟨_, _, .here, .here, hm⟩
    | there hc' =>
      obtain ⟨m1, m2, h1, h2, hm'⟩ := ih hc'
      exact ⟨m1, m2, .there h1, .there h2, hm'⟩
  | lock _ ih =>
    cases hc with
    | lock hc' =>
      obtain ⟨m1, m2, h1, h2, hm⟩ := ih hc'
      exact ⟨m1, m2, .lock h1, .lock h2, hm⟩

/-- A cvar lookup in `Γ1` lifts to corresponding lookups in `Γ2` and the composed
context `Γ3`, with use modes related by `UseMode.SeqComp`. -/
theorem Ctx.SeqComp.lookup_cvar_left
  {Γ1 Γ2 Γ3 : Ctx s} {c : BVar s .cvar} {m1 : UseMode}
  {cb : CaptureBound s} {locked : Bool}
  (h : Ctx.SeqComp Γ1 Γ2 Γ3)
  (hc1 : Γ1.LookupCVar c m1 cb locked) :
  ∃ m2 m3,
    Γ2.LookupCVar c m2 cb locked ∧
    Γ3.LookupCVar c m3 cb locked ∧
    UseMode.SeqComp m1 m2 m3 := by
  induction h generalizing m1 locked with
  | empty => cases hc1
  | push_var _ ih =>
    cases hc1 with
    | there hc1' =>
      obtain ⟨m2, m3, h2, h3, hm⟩ := ih hc1'
      exact ⟨m2, m3, .there h2, .there h3, hm⟩
  | push_tvar _ ih =>
    cases hc1 with
    | there hc1' =>
      obtain ⟨m2, m3, h2, h3, hm⟩ := ih hc1'
      exact ⟨m2, m3, .there h2, .there h3, hm⟩
  | push_cvar _ hm0 ih =>
    cases hc1 with
    | here => exact ⟨_, _, .here, .here, hm0⟩
    | there hc1' =>
      obtain ⟨m2, m3, h2, h3, hm⟩ := ih hc1'
      exact ⟨m2, m3, .there h2, .there h3, hm⟩
  | lock _ ih =>
    cases hc1 with
    | lock hc1' =>
      obtain ⟨m2, m3, h2, h3, hm⟩ := ih hc1'
      exact ⟨m2, m3, .lock h2, .lock h3, hm⟩

/-- Conversely, lookups in `Γ1` and `Γ2` (with composing use modes) lift to a
lookup in the composed context `Γ3`. -/
theorem Ctx.SeqComp.lookup_cvar_compose
  {Γ1 Γ2 Γ3 : Ctx s} {c : BVar s .cvar} {m1 m2 m3 : UseMode}
  {cb : CaptureBound s} {locked : Bool}
  (h : Ctx.SeqComp Γ1 Γ2 Γ3)
  (hc1 : Γ1.LookupCVar c m1 cb locked)
  (hc2 : Γ2.LookupCVar c m2 cb locked)
  (hm : UseMode.SeqComp m1 m2 m3) :
  Γ3.LookupCVar c m3 cb locked := by
  obtain ⟨m2', m3', hc2', hc3', hm'⟩ := h.lookup_cvar_left hc1
  obtain ⟨hm2, _, _⟩ := Ctx.lookup_cvar_det hc2 hc2'
  subst hm2
  rw [UseMode.SeqComp.det hm hm']
  exact hc3'

end Consume
