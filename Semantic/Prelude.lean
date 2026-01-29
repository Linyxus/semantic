import Mathlib.Data.Finset.Basic

class HasDenotation (T : Type) (Env : Type) (Denot : outParam Type) where
  interp : Env -> T -> Denot

notation:max "⟦" T "⟧_[" ρ "]" => HasDenotation.interp ρ T

class HasExpDenotation (T : Type) (Env : Type) (Denot : outParam Type) where
  interp : Env -> T -> Denot

notation:max "⟦" T "⟧e_[" ρ "]" => HasExpDenotation.interp ρ T

/-- `easy` is an alias of `assumption`. -/
macro "easy" : tactic => `(tactic| assumption)
/-- `apply!` applies a hypothesis and `easy` on all generated subgoals. -/
macro "apply!" e:term : tactic => `(tactic| apply $e <;> easy)
/-- `apply?` applies a hypothesis and try to `easy` on all generated subgoals. -/
macro "apply?" e:term : tactic => `(tactic| apply $e <;> try easy)

structure Finmap (K V : Type) where
  apply : K -> Option V
  dom : Finset K
  hasdom : ∀ k, k ∈ dom ↔ ∃ v, apply k = some v

namespace Finmap

def extend (m : Finmap a b) (k : a) (v : b) : Finmap a b := sorry

end Finmap
