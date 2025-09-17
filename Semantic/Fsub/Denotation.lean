import Semantic.Fsub.Eval

namespace Fsub

mutual

def Ty.val_denot : Ty {} -> Store -> Exp {} -> Prop
| .top => fun s e => True
| .singleton x => fun s e => e = .var x
| .arrow T U => fun s e => sorry
| .poly T U => fun s e => sorry

def Ty.exp_denot : Ty {} -> Store -> Exp {} -> Prop :=
  fun T s e =>
    ∃ s' v,
      Reduce s e s' v ∧
      Ty.val_denot T s' v

end

end Fsub
