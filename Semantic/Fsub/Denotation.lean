import Semantic.Fsub.Eval

namespace Fsub

mutual

-- Termination checking fails
def Ty.val_denot : Ty {} -> Store -> Exp {} -> Prop
| .top => fun s e => True
| .singleton x => fun s e => False  -- A value cannot be a singleton
| .arrow T U => fun s e =>
  ∃ T0 e0,
    e = .abs T0 e0 ∧
    (∀ x,
      Ty.var_denot T s x ->
      Ty.val_denot (U.subst (Subst.openVar x)) s (e0.subst (Subst.openVar x)))
| .poly T U => fun s e => sorry

def Ty.var_denot : Ty {} -> Store -> Var {} -> Prop
| .singleton x => fun s e => e = x
| other => fun s e =>
  ∃ fx v hv,
    e = .free fx ∧
    s.lookup fx = some ⟨v, hv⟩ ∧
    Ty.val_denot other s v

def Ty.exp_denot : Ty {} -> Store -> Exp {} -> Prop :=
  fun T s e =>
    ∃ s' v,
      Reduce s e s' v ∧
      Ty.val_denot T s' v

end

end Fsub
