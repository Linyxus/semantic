class HasDenotation (T : Type) (Env : Type) (Denot : outParam Type) where
  interp : Env -> T -> Denot

notation:max "⟦" T "⟧_[" ρ "]" => HasDenotation.interp ρ T

class HasExpDenotation (T : Type) (Env : Type) (Denot : outParam Type) where
  interp : Env -> T -> Denot

notation:max "⟦" T "⟧e_[" ρ "]" => HasExpDenotation.interp ρ T
