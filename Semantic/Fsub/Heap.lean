import Semantic.Fsub.Syntax

namespace Fsub

-- A heap is a function from locations to values
def Heap : Type := Nat -> Option (Val {})

def Heap.empty : Heap := fun _ => none

instance Heap.instEmptyCollection : EmptyCollection Heap := ⟨Heap.empty⟩

def Heap.extend (h : Heap) (l : Nat) (v : Val {}) : Heap :=
  fun l' => if l' = l then some v else h l'

def Heap.subsumes (big small : Heap) : Prop :=
  ∀ l v, small l = some v -> big l = some v

theorem Heap.subsumes_refl (h : Heap) : h.subsumes h :=
  fun _ _ => id

/-- Heap predicate. -/
def Hprop := Heap -> Prop

/-- Postcondition. -/
def Hpost := Exp {} -> Hprop

/-- Monotonicity of postconditions. -/
def Hpost.is_monotonic (Q : Hpost) : Prop :=
  ∀ {h1 h2 : Heap} {e},
    h2.subsumes h1 ->
    Q e h1 ->
    Q e h2

def Hpost.entails (Q1 Q2 : Hpost) : Prop :=
  ∀ h e,
    Q1 e h ->
    Q2 e h

def Hpost.entails_refl (Q : Hpost) : Q.entails Q :=
  fun _ _ => id

def Heap.subsumes_trans {h1 h2 h3 : Heap}
  (h12 : h1.subsumes h2)
  (h23 : h2.subsumes h3) :
  h1.subsumes h3 :=
  fun l v hlookup => h12 l v (h23 l v hlookup)

theorem Heap.extend_lookup_eq
  (h : Heap) (l : Nat) (v : Val {}) :
  (h.extend l v) l = some v := by
  simp [Heap.extend]

theorem Heap.extend_subsumes {H : Heap} {l : Nat}
  (hfresh : H l = none) :
  (H.extend l v).subsumes H := by
  intro l' v' hlookup
  simp only [Heap.extend]
  split
  · next heq => rw [heq, hfresh] at hlookup; contradiction
  · exact hlookup

end Fsub
