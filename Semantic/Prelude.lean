class HasDenotation (T : Type) (Env : Type) (TEnv : Type) (Denot : outParam Type) where
  interp : Env -> TEnv -> T -> Denot

notation:max "⟦" T "⟧_[" ρ "," φ "]" => HasDenotation.interp ρ φ T

class HasExpDenotation (T : Type) (Env : Type) (TEnv : Type) (Denot : outParam Type) where
  interp : Env -> TEnv -> T -> Denot

notation:max "⟦" T "⟧e_[" ρ "," φ "]" => HasExpDenotation.interp ρ φ T
