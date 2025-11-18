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

/-- The size of a signature. -/
def Sig.size : Sig -> Nat :=
  fun s => s.length

/-- Debruijn-level of a bound variable. -/
def BVar.level : BVar s k -> Nat
| .here => s.length
| .there x => x.level

def CaptureSet.to_platform_capability_set : CaptureSet (Sig.platform_of N) -> CapabilitySet
| .empty => .empty
| .union cs1 cs2 =>
    (cs1.to_platform_capability_set) ∪ (cs2.to_platform_capability_set)
| .var x => sorry
| .cvar c => sorry

end CC
