import Semantic.CC.Fundamental
import Semantic.CC.Semantics.Props
namespace CC

/-! The following defines _platforms_. -/

/-- Context signature of a platform of `n` ground capabilities. -/
def Sig.platform_of : Nat -> Sig
| 0 => {}
| n+1 => ((Sig.platform_of n),C),x

/-- A platform context with `n` ground capabilities. -/
def Ctx.platform_of : (n : Nat) -> Ctx (Sig.platform_of n)
| 0 => .empty
| n+1 => ((Ctx.platform_of n),C<:.unbound),x:(.capt (.cvar .here) .cap)

/-- A platform heap with `n` ground capabilities. -/
def Heap.platform_of (N : Nat) : Heap :=
  fun i =>
    if i < N then
      .some .capability
    else
      .none

end CC
