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

def empty : Finmap a b where
  apply := fun _ => none
  dom := ∅
  hasdom := by simp

def extend [DecidableEq a] (m : Finmap a b) (k : a) (v : b) : Finmap a b where
  apply := fun k' => if k' = k then some v else m.apply k'
  dom := insert k m.dom
  hasdom := by
    intro k'
    simp only [Finset.mem_insert]
    constructor
    · rintro (rfl | h)
      · exact ⟨v, if_pos rfl⟩
      · obtain ⟨v', hv'⟩ := (m.hasdom k').mp h
        by_cases hk : k' = k
        · exact ⟨v, if_pos hk⟩
        · exact ⟨v', by simp [hk, hv']⟩
    · intro ⟨v', hv'⟩
      by_cases hk : k' = k
      · left; exact hk
      · right
        simp only [hk, ↓reduceIte] at hv'
        exact (m.hasdom k').mpr ⟨v', hv'⟩

end Finmap
