import Semantic.FsubNext.Syntax

namespace FsubNext

-- A heap is a function from locations to values
def Heap : Type := Nat -> Option (Val {})

def Heap.empty : Heap := fun _ => none

instance Heap.instEmptyCollection : EmptyCollection Heap := ⟨Heap.empty⟩

def Heap.extend (h : Heap) (l : Nat) (v : Val {}) : Heap :=
  fun l' => if l' = l then some v else h l'

def Heap.subsumes (big small : Heap) : Prop :=
  ∀ l v, small l = some v -> big l = some v

theorem Heap.subsumes_refl (h : Heap) : h.subsumes h := by
  intros l v hlookup
  exact hlookup

/-- Heap predicate. -/
def Hprop := Heap -> Prop

/-- Postcondition. -/
def Hpost := Exp {} -> Hprop

end FsubNext
