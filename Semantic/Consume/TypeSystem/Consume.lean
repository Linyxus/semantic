import Semantic.Consume.Syntax
import Semantic.Consume.Substitution
import Semantic.Consume.TypeSystem.BasicProps

namespace Consume

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
  | lock =>
    cases h2 with
    | lock => rfl

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
  | lock => exact hx

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
  | lock => exact hx

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
  | lock => exact hx

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
  | lock => exact hx

end Consume
