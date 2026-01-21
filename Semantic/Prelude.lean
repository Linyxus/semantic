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
