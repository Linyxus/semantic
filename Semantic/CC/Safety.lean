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

/-- Convert a capture set in a platform context to a concrete capability set.
  Platform contexts have `N` capabilities arranged as pairs `(C, x)` at levels
  `(0,1), (2,3), ..., (2N-2, 2N-1)`, where capability `i` corresponds to
  variables at levels `2i` and `2i+1`. Bound variables map via `level / 2`,
  while free variables directly reference heap locations. -/
def CaptureSet.to_platform_capability_set : CaptureSet (Sig.platform_of N) -> CapabilitySet
| .empty => .empty
| .union cs1 cs2 =>
    (cs1.to_platform_capability_set) ∪ (cs2.to_platform_capability_set)
| .var x =>
    match x with
    | .bound b => .cap (b.level / 2)
    | .free n => .cap n
| .cvar c => .cap (c.level / 2)

end CC
