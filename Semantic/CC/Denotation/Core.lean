import Semantic.CC.Eval
import Semantic.CC.TypeSystem
import Semantic.Prelude

namespace CC

def resolve : Heap -> Exp {} -> Option (Exp {})
| s, .var (.free x) =>
  match s x with
  | some (.val v) => some v.unwrap
  | _ => none
| s, .var (.bound x) => by cases x
| _, other => some other

/-- Denotation of types. -/
def Denot := Heap -> Exp {} -> Prop

/-- Pre-denotation -/
def PreDenot := CapabilitySet -> Denot

def Denot.as_post (d : Denot) : Hpost :=
  fun e h => d h e

def Denot.as_mpost (d : Denot) : Mpost :=
  fun e m => d m.heap e

/-- Temporary helper: wrap a Heap in a Memory with a sorried well-formedness proof.
    TODO: This should be removed once the denotational semantics is properly updated
    to work with well-formed heaps. -/
def Heap.to_memory (h : Heap) : Memory :=
  { heap := h, wf := sorry }

def Denot.is_monotonic (d : Denot) : Prop :=
  ∀ {h1 h2 : Heap} {e},
    h2.subsumes h1 ->
    d h1 e ->
    d h2 e

def Denot.is_transparent (d : Denot) : Prop :=
  ∀ {h : Heap} {x : Nat} {v},
    h x = some (.val v) ->
    d h v.unwrap ->
    d h (.var (.free x))

def Denot.is_proper (d : Denot) : Prop :=
  d.is_monotonic ∧ d.is_transparent

def PreDenot.is_proper (pd : PreDenot) : Prop :=
  ∀ C, (pd C).is_proper

def Denot.Imply (d1 d2 : Denot) : Prop :=
  ∀ s e,
    (d1 s e) ->
    (d2 s e)

def PreDenot.Imply (pd1 pd2 : PreDenot) : Prop :=
  ∀ C,
    (pd1 C).Imply (pd2 C)

def Denot.ImplyAt (d1 : Denot) (h : Heap) (d2 : Denot) : Prop :=
  ∀ e, d1 h e -> d2 h e

def PreDenot.ImplyAt (pd1 pd2 : PreDenot) (h : Heap) : Prop :=
  ∀ C, (pd1 C).ImplyAt h (pd2 C)

def Denot.ImplyAfter (d1 : Denot) (h : Heap) (d2 : Denot) : Prop :=
  ∀ h', h'.subsumes h -> d1.ImplyAt h' d2

def PreDenot.ImplyAfter (pd1 : PreDenot) (h : Heap) (pd2 : PreDenot) : Prop :=
  ∀ C, (pd1 C).ImplyAfter h (pd2 C)

theorem Denot.imply_implyat {d1 d2 : Denot}
  (himp : d1.Imply d2) :
  d1.ImplyAt h d2 := by
  intro e h1
  apply himp h e h1

theorem Denot.implyat_trans
  {d1 d2 : Denot}
  (himp1 : d1.ImplyAt h d2)
  (himp2 : d2.ImplyAt h d3) :
  d1.ImplyAt h d3 := by
  intro e h1
  apply himp2 e (himp1 e h1)

lemma Denot.imply_after_to_m_entails_after {d1 d2 : Denot}
  {m : Memory}
  (himp : d1.ImplyAfter m.heap d2) :
  d1.as_mpost.entails_after m d2.as_mpost := by
  intro m' hsub
  unfold Mpost.entails_at Denot.as_mpost
  intro e h1
  apply himp m'.heap hsub e h1

lemma Denot.imply_after_subsumes {d1 d2 : Denot}
  (himp : d1.ImplyAfter h1 d2)
  (hheap : h2.subsumes h1) :
  d1.ImplyAfter h2 d2 := by
  intro H hs
  apply himp H
  apply Heap.subsumes_trans hs hheap

lemma Denot.imply_after_to_imply_at {d1 d2 : Denot}
  (himp : d1.ImplyAfter h d2) :
  d1.ImplyAt h d2 := by
  intro e h1
  apply himp h (Heap.subsumes_refl h) e h1

lemma Denot.imply_after_trans {d1 d2 d3 : Denot}
  (himp1 : d1.ImplyAfter h d2)
  (himp2 : d2.ImplyAfter h d3) :
  d1.ImplyAfter h d3 := by
  intro h' hsub e h1
  apply himp2 h' hsub
  apply himp1 h' hsub e h1

lemma Denot.apply_imply_at {d1 d2 : Denot}
  (ht : d1 h e)
  (himp : d1.ImplyAt h d2) :
  d2 h e := by
  apply himp e ht

/-- Heap topology maps memory locations to "reachable" capabilities. -/
def HeapTopology : Type := Nat -> CapabilitySet

inductive TypeInfo : Kind -> Type where
| var : Nat -> TypeInfo .var
| tvar : PreDenot -> TypeInfo .tvar
| cvar : CapabilitySet -> TypeInfo .cvar

inductive TypeEnv : Sig -> Type where
| empty : TypeEnv {}
| extend :
  TypeEnv s ->
  TypeInfo k ->
  TypeEnv (s,,k)

def TypeEnv.extend_var (Γ : TypeEnv s) (x : Nat) : TypeEnv (s,x) :=
  Γ.extend (.var x)

def TypeEnv.extend_tvar (Γ : TypeEnv s) (T : PreDenot) : TypeEnv (s,X) :=
  Γ.extend (.tvar T)

def TypeEnv.extend_cvar (Γ : TypeEnv s) (underlying : CapabilitySet) : TypeEnv (s,C) :=
  Γ.extend (.cvar underlying)

def HeapTopology.extend : HeapTopology -> Nat -> CapabilitySet -> HeapTopology
| topo, x, c =>
  fun y => if y = x then c else topo y

def TypeEnv.lookup : (Γ : TypeEnv s) -> (x : BVar s k) -> TypeInfo k
| .extend _ info, .here => info
| .extend Γ _,    .there x => Γ.lookup x

def TypeEnv.lookup_var (Γ : TypeEnv s) (x : BVar s .var) : Nat :=
  match Γ.lookup x with
  | .var y => y

def TypeEnv.lookup_tvar (Γ : TypeEnv s) (x : BVar s .tvar) : PreDenot :=
  match Γ.lookup x with
  | .tvar T => T

def TypeEnv.lookup_cvar (Γ : TypeEnv s) (x : BVar s .cvar) : CapabilitySet :=
  match Γ.lookup x with
  | .cvar c => c

def CaptureSet.denot : TypeEnv s -> HeapTopology -> CaptureSet s -> CapabilitySet
| _, _, .empty => CapabilitySet.empty
| env, topo, .union cs1 cs2 =>
  (cs1.denot env topo) ∪ (cs2.denot env topo)
| env, topo, .var (.bound x) => topo (env.lookup_var x)
| _, _, .var (.free x) => {x}
| env, _, .cvar c => env.lookup_cvar c

def CaptureBound.denot : TypeEnv s -> HeapTopology -> CaptureBound s -> CapabilitySet
| _, _, .unbound => CapabilitySet.any
| env, topo, .bound cs => cs.denot env topo

mutual

def Ty.shape_val_denot : TypeEnv s -> HeapTopology -> Ty .shape s -> PreDenot
| _, _, .top => fun _ _ _ => True
| env, _, .tvar X => env.lookup_tvar X
| _, _, .unit => fun _ H e => resolve H e = some .unit
| _, _, .cap => fun A H e =>
  ∃ label : Nat,
    e = .var (.free label) ∧
    H label = some .capability ∧
    label ∈ A
| env, φ, .arrow T1 T2 => fun A H e =>
  ∃ cs T0 t0,
    resolve H e = some (.abs cs T0 t0) ∧
    (∀ (arg : Nat) (H' : Heap),
      H'.subsumes H ->
      Ty.capt_val_denot env φ T1 H' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg)
        (φ.extend arg (T1.captureSet.denot env φ))
        T2 (A ∪ T1.captureSet.denot env φ) H' (t0.subst (Subst.openVar (.free arg))))
| env, φ, .poly T1 T2 => fun A H e =>
  ∃ cs S0 t0,
    resolve H e = some (.tabs cs S0 t0) ∧
    (∀ (H' : Heap) (denot : PreDenot),
      H'.subsumes H ->
      denot.is_proper ->
      denot.ImplyAfter H' (Ty.shape_val_denot env φ T1) ->
      Ty.exi_exp_denot
        (env.extend_tvar denot)
        φ
        T2 A H' (t0.subst (Subst.openTVar .top)))
| env, φ, .cpoly B T => fun A H e =>
  ∃ cs B0 t0,
    resolve H e = some (.cabs cs B0 t0) ∧
    (∀ (H' : Heap) (A0 : CapabilitySet),
      H'.subsumes H ->
      (A0 ⊆ B.denot env φ) ->
      Ty.exi_exp_denot
        (env.extend_cvar A0)
        φ
        T A H' (t0.subst (Subst.openCVar .empty)))

def Ty.capt_val_denot : TypeEnv s -> HeapTopology -> Ty .capt s -> Denot
| ρ, φ, .capt C S => Ty.shape_val_denot ρ φ S (C.denot ρ φ)

def Ty.exi_val_denot : TypeEnv s -> HeapTopology -> Ty .exi s -> Denot
| ρ, φ, .typ T => Ty.capt_val_denot ρ φ T
| ρ, φ, .exi T => fun H e =>
  ∃ (A : CapabilitySet),
    Ty.capt_val_denot (ρ.extend_cvar A) φ T H e

def Ty.capt_exp_denot : TypeEnv s -> HeapTopology -> Ty .capt s -> PreDenot
| ρ, φ, T => fun A H e =>
  Eval A H.to_memory e (Ty.capt_val_denot ρ φ T).as_mpost

def Ty.exi_exp_denot : TypeEnv s -> HeapTopology -> Ty .exi s -> PreDenot
| ρ, φ, T => fun A H e =>
  Eval A H.to_memory e (Ty.exi_val_denot ρ φ T).as_mpost

end

@[simp]
instance instCaptHasDenotation :
  HasDenotation (Ty .capt s) (TypeEnv s) HeapTopology Denot where
  interp := Ty.capt_val_denot

@[simp]
instance instCaptHasExpDenotation :
  HasExpDenotation (Ty .capt s) (TypeEnv s) HeapTopology PreDenot where
  interp := Ty.capt_exp_denot

@[simp]
instance instExiHasDenotation :
  HasDenotation (Ty .exi s) (TypeEnv s) HeapTopology Denot where
  interp := Ty.exi_val_denot

@[simp]
instance instExiHasExpDenotation :
  HasExpDenotation (Ty .exi s) (TypeEnv s) HeapTopology PreDenot where
  interp := Ty.exi_exp_denot

@[simp]
instance instShapeHasDenotation :
  HasDenotation (Ty .shape s) (TypeEnv s) HeapTopology PreDenot where
  interp := Ty.shape_val_denot

@[simp]
instance instCaptureSetHasDenotation :
  HasDenotation (CaptureSet s) (TypeEnv s) HeapTopology CapabilitySet where
  interp := CaptureSet.denot

@[simp]
instance instCaptureBoundHasDenotation :
  HasDenotation (CaptureBound s) (TypeEnv s) HeapTopology CapabilitySet where
  interp := CaptureBound.denot

def EnvTyping : Ctx s -> TypeEnv s -> HeapTopology -> Heap -> Prop
| .empty, .empty, _, _ => True
| .push Γ (.var T), .extend env (.var n), φ, H =>
  ⟦T⟧_[env, φ] H (.var (.free n)) ∧
  φ n = ⟦T.captureSet⟧_[env, φ] ∧
  EnvTyping Γ env φ H
| .push Γ (.tvar S), .extend env (.tvar denot), φ, H =>
  denot.is_proper ∧
  denot.ImplyAfter H ⟦S⟧_[env, φ] ∧
  EnvTyping Γ env φ H
| .push Γ (.cvar B), .extend env (.cvar access), φ, H =>
  (access ⊆ ⟦B⟧_[env, φ]) ∧
  EnvTyping Γ env φ H

def Subst.from_TypeEnv (env : TypeEnv s) : Subst s {} where
  var := fun x => .free (env.lookup_var x)
  tvar := fun _ => .top
  cvar := fun _ => {}

def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ φ H,
    EnvTyping Γ ρ φ H ->
    ⟦E⟧e_[ρ,φ] (C.denot ρ φ) H (e.subst (Subst.from_TypeEnv ρ))

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping C Γ e T

theorem Subst.from_TypeEnv_weaken_open {env : TypeEnv s} {x : Nat} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free x)) =
    Subst.from_TypeEnv (env.extend_var x) := by
  apply Subst.funext
  · intro y
    cases y <;> rfl
  · intro X
    cases X
    rfl
  · intro C
    cases C
    rfl

theorem Exp.from_TypeEnv_weaken_open {e : Exp (s,x)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free x)) =
    e.subst (Subst.from_TypeEnv (env.extend_var x)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_TypeEnv_weaken_open]

theorem Subst.from_TypeEnv_weaken_open_tvar {env : TypeEnv s} {d : PreDenot} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openTVar .top) =
    Subst.from_TypeEnv (env.extend_tvar d) := by
  apply Subst.funext
  · intro x
    cases x
    rfl
  · intro X
    cases X
    case here => rfl
    case there X' =>
      simp [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openTVar,
        TypeEnv.extend_tvar, Ty.subst, Ty.rename]
  · intro C
    cases C
    rfl

theorem Exp.from_TypeEnv_weaken_open_tvar
  {env : TypeEnv s} {d : PreDenot} {e : Exp (s,X)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openTVar .top) =
    e.subst (Subst.from_TypeEnv (env.extend_tvar d)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_TypeEnv_weaken_open_tvar]

theorem Subst.from_TypeEnv_weaken_open_cvar {env : TypeEnv s} {c : CapabilitySet} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openCVar .empty) =
    Subst.from_TypeEnv (env.extend_cvar c) := by
  apply Subst.funext
  · intro x
    cases x
    rfl
  · intro X
    cases X
    rfl
  · intro C
    cases C
    case here => rfl
    case there C' =>
      simp [Subst.comp, Subst.lift, Subst.from_TypeEnv, Subst.openCVar,
        TypeEnv.extend_cvar, CaptureSet.subst, CaptureSet.rename]

theorem Exp.from_TypeEnv_weaken_open_cvar
  {env : TypeEnv s} {c : CapabilitySet} {e : Exp (s,C)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openCVar .empty) =
    e.subst (Subst.from_TypeEnv (env.extend_cvar c)) := by
  rw [Exp.subst_comp]
  rw [Subst.from_TypeEnv_weaken_open_cvar]

def Denot.Equiv (d1 d2 : Denot) : Prop :=
  ∀ s e,
    (d1 s e) ↔ (d2 s e)

instance Denot.instHasEquiv : HasEquiv Denot where
  Equiv := Denot.Equiv

def Denot.equiv_refl (d : Denot) : d ≈ d := by
  intro s e
  constructor
  · intro h
    exact h
  · intro h
    exact h

def Denot.equiv_symm (d1 d2 : Denot) : d1 ≈ d2 -> d2 ≈ d1 := by
  intro h
  intro s e
  constructor
  · intro h0
    apply (h s e).mpr h0
  · intro h0
    apply (h s e).mp h0

def Denot.equiv_trans (d1 d2 d3 : Denot) : d1 ≈ d2 -> d2 ≈ d3 -> d1 ≈ d3 := by
  intro h12
  intro h23
  intro s e
  have h1 := h12 s e
  have h2 := h23 s e
  grind

theorem Denot.eq_to_equiv (d1 d2 : Denot) : d1 = d2 -> d1 ≈ d2 := by
  intro h
  intro s e
  grind

theorem Denot.equiv_ltr {d1 d2 : Denot}
  (heqv : d1 ≈ d2)
  (h1 : d1 s e) :
  d2 s e := by
  apply (heqv s e).mp h1

theorem Denot.equiv_rtl {d1 d2 : Denot}
  (heqv : d1 ≈ d2)
  (h2 : d2 s e) :
  d1 s e := by
  apply (heqv s e).mpr h2

theorem Denot.equiv_to_imply {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  (d1.Imply d2) ∧ (d2.Imply d1) := by
  constructor
  · intro s e h
    apply (heqv s e).mp h
  · intro s e h
    apply (heqv s e).mpr h

theorem Denot.equiv_to_imply_l {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  d1.Imply d2 := (Denot.equiv_to_imply heqv).1

theorem Denot.equiv_to_imply_r {d1 d2 : Denot}
  (heqv : d1 ≈ d2) :
  d2.Imply d1 := (Denot.equiv_to_imply heqv).2

theorem Denot.imply_to_entails (d1 d2 : Denot)
  (himp : d1.Imply d2) :
  d1.as_post.entails d2.as_post := by
  intro h e h1
  apply himp h e h1

/- Equivalence for PreDenot -/
def PreDenot.Equiv (pd1 pd2 : PreDenot) : Prop :=
  ∀ A, (pd1 A) ≈ (pd2 A)

instance PreDenot.instHasEquiv : HasEquiv PreDenot where
  Equiv := PreDenot.Equiv

theorem PreDenot.equiv_def {pd1 pd2 : PreDenot} :
  pd1 ≈ pd2 ↔ ∀ A s e, (pd1 A s e) ↔ (pd2 A s e) := by
  constructor
  · intro h A s e
    exact (h A) s e
  · intro h A
    intro s e
    exact h A s e

theorem PreDenot.eq_to_equiv {pd1 pd2 : PreDenot} (h : pd1 = pd2) : pd1 ≈ pd2 := by
  intro A
  intro s e
  rw [h]

theorem PreDenot.equiv_refl (pd : PreDenot) : pd ≈ pd := by
  intro A
  apply Denot.equiv_refl

theorem PreDenot.equiv_symm (pd1 pd2 : PreDenot) : pd1 ≈ pd2 -> pd2 ≈ pd1 := by
  intro h A
  apply Denot.equiv_symm
  exact h A

theorem PreDenot.equiv_trans (pd1 pd2 pd3 : PreDenot) : pd1 ≈ pd2 -> pd2 ≈ pd3 -> pd1 ≈ pd3 := by
  intro h12 h23 A
  apply Denot.equiv_trans _ (pd2 A) _
  · exact h12 A
  · exact h23 A

theorem Denot.imply_refl (d : Denot) : d.Imply d := by
  intro s e h
  exact h

theorem Denot.imply_trans {d1 d2 d3 : Denot}
  (h1 : d1.Imply d2)
  (h2 : d2.Imply d3) :
  d1.Imply d3 := by
  intro s e h
  aesop

theorem resolve_var_heap_some
  (hheap : heap x = some (.val v)) :
  resolve heap (.var (.free x)) = some v.unwrap := by
  simp [resolve, hheap]

theorem resolve_val
  (hval : v.IsVal) :
  resolve heap v = some v := by
  cases hval <;> rfl

theorem resolve_var_heap_trans
  (hheap : heap x = some (.val v)) :
  resolve heap (.var (.free x)) = resolve heap (v.unwrap) := by
  rw [resolve_var_heap_some hheap]
  rw [resolve_val v.isVal.to_IsVal]

theorem resolve_var_or_val
  (hv : resolve store e = some v) :
  (∃ x, e = .var x) ∨ e = v := by
  cases e
  all_goals try (solve | aesop | simp [resolve] at hv; aesop)

theorem resolve_ans_to_val
  (hv : resolve store e = some v)
  (hans : v.IsAns) :
  e.IsAns := by
  cases (resolve_var_or_val hv)
  case inl h =>
    have ⟨x, h⟩ := h
    rw [h]
    apply Exp.IsAns.is_var
  case inr h => aesop

def PreDenot.is_monotonic (pd : PreDenot) : Prop :=
  ∀ C, (pd C).is_monotonic

def PreDenot.is_transparent (pd : PreDenot) : Prop :=
  ∀ C, (pd C).is_transparent

def TypeEnv.is_monotonic (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_monotonic

def TypeEnv.is_transparent (env : TypeEnv s) : Prop :=
  ∀ (X : BVar s .tvar),
    (env.lookup_tvar X).is_transparent

theorem typed_env_is_monotonic
  (ht : EnvTyping Γ env φ store) :
  env.is_monotonic := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_monotonic]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht
          have ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_monotonic] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_monotonic] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            -- hproper says d.is_proper, which means ∀ C, (d C).is_proper
            -- We need d.is_monotonic, which means ∀ C, (d C).is_monotonic
            intro C
            exact (hproper C).1
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar access =>
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_monotonic] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x

def Denot.as_post_is_monotonic {d : Denot}
  (hmon : d.is_monotonic) :
  d.as_post.is_monotonic := by
  intro h1 h2 e hsub hde
  apply hmon hsub hde

theorem typed_env_is_transparent
  (ht : EnvTyping Γ env φ store) :
  env.is_transparent := by
  induction Γ with
  | empty =>
    cases env with
    | empty =>
      simp [TypeEnv.is_transparent]
      intro x
      cases x
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht
          have ⟨_, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht
          have ⟨hproper, _, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | here =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            -- hproper says d.is_proper, which means ∀ C, (d C).is_proper
            -- We need d.is_transparent, which means ∀ C, (d C).is_transparent
            intro C
            exact (hproper C).2
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x
      | cvar B =>
        cases info with
        | cvar access =>
          simp [EnvTyping] at ht
          have ⟨_, ht'⟩ := ht
          have ih_result := ih ht'
          simp [TypeEnv.is_transparent] at ih_result ⊢
          intro x
          cases x with
          | there x =>
            simp [TypeEnv.lookup_tvar, TypeEnv.lookup]
            exact ih_result x

theorem shape_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env φ T).is_transparent := by
  cases T with
  | top =>
    intro C h x v hx ht
    simp [Ty.shape_val_denot]
  | tvar X =>
    intro C
    simp [Ty.shape_val_denot]
    exact henv X C
  | unit =>
    intro C h x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    rw [resolve_var_heap_trans hx]
    exact ht
  | cap =>
    intro C h x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨label, hlabel, hcap, hmem⟩ := ht
    -- v.unwrap = .var (.free label), but v.isVal says it's a simple value
    -- Variables are not simple values, so this is a contradiction
    have hval := v.isVal
    rw [hlabel] at hval
    cases hval
  | arrow T1 T2 =>
    intro C h x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have heq := resolve_var_heap_trans hx
    rw [heq]
    exact ht
  | poly T1 T2 =>
    intro C h x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have heq := resolve_var_heap_trans hx
    rw [heq]
    exact ht
  | cpoly B T =>
    intro C h x v hx ht
    simp [Ty.shape_val_denot] at ht ⊢
    have heq := resolve_var_heap_trans hx
    rw [heq]
    exact ht

theorem capt_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env φ T).is_transparent := by
  cases T with
  | capt C S =>
    simp [Ty.capt_val_denot]
    exact shape_val_denot_is_transparent henv S (C.denot env φ)

theorem exi_val_denot_is_transparent {env : TypeEnv s}
  (henv : TypeEnv.is_transparent env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env φ T).is_transparent := by
  cases T with
  | typ T =>
    simp [Ty.exi_val_denot]
    exact capt_val_denot_is_transparent henv T
  | exi T =>
    intro h x v hx ht
    simp [Ty.exi_val_denot] at ht ⊢
    have ⟨A, hA⟩ := ht
    use A
    -- Need to show transparency is preserved when extending with cvar
    have henv' : (env.extend_cvar A).is_transparent := by
      intro X
      cases X with
      | there X' =>
        simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
        exact henv X'
    exact capt_val_denot_is_transparent henv' T hx hA

mutual

def shape_val_denot_is_monotonic {env : TypeEnv s} {φ : HeapTopology}
  (henv : TypeEnv.is_monotonic env)
  (T : Ty .shape s) :
  (Ty.shape_val_denot env φ T).is_monotonic := by
  intro C
  cases T with
  | top =>
    intro h1 h2 e hheap ht
    simp [Ty.shape_val_denot] at ht ⊢
  | tvar X =>
    simp [Ty.shape_val_denot]
    exact henv X C
  | unit =>
    intro h1 h2 e hheap ht
    simp [Ty.shape_val_denot] at ht ⊢
    cases e with
    | var x =>
      cases x with
      | free fx =>
        simp [resolve] at ht ⊢
        cases hres : h1 fx with
        | none => simp [hres] at ht
        | some v =>
          simp [hres] at ht
          have := hheap fx v hres
          simp [this, ht]
      | bound bx => cases bx
    | unit => simp [resolve] at ht ⊢
    | abs _ _ _ => simp [resolve] at ht
    | tabs _ _ _ => simp [resolve] at ht
    | cabs _ _ _ => simp [resolve] at ht
    | pack _ _ => simp [resolve] at ht
    | unpack _ _ => simp [resolve] at ht
    | app _ _ => simp [resolve] at ht
    | tapp _ _ => simp [resolve] at ht
    | capp _ _ => simp [resolve] at ht
    | letin _ _ => simp [resolve] at ht
  | cap =>
    intro h1 h2 e hheap ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨label, heq, hcap, hmem⟩ := ht
    use label
    constructor
    · exact heq
    · constructor
      · have := hheap label .capability hcap
        exact this
      · exact hmem
  | arrow T1 T2 =>
    intro h1 h2 e hheap ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨cs, T0, t0, hr, hfun⟩ := ht
    use cs, T0, t0
    constructor
    · cases e with
      | var x =>
        cases x with
        | free fx =>
          simp [resolve] at hr ⊢
          cases hres : h1 fx with
          | none => simp [hres] at hr
          | some v =>
            simp [hres] at hr
            have := hheap fx v hres
            simp [this, hr]
        | bound bx => cases bx
      | abs _ _ _ => simp [resolve] at hr ⊢; exact hr
      | tabs _ _ _ => simp [resolve] at hr
      | cabs _ _ _ => simp [resolve] at hr
      | pack _ _ => simp [resolve] at hr
      | unit => simp [resolve] at hr
      | unpack _ _ => simp [resolve] at hr
      | app _ _ => simp [resolve] at hr
      | tapp _ _ => simp [resolve] at hr
      | capp _ _ => simp [resolve] at hr
      | letin _ _ => simp [resolve] at hr
    · intro arg H' hs' harg
      have hs0 := Heap.subsumes_trans hs' hheap
      -- harg is already in H', so we can use it directly
      apply hfun arg H' hs0 harg
  | poly T1 T2 =>
    intro h1 h2 e hheap ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨cs, S0, t0, hr, hfun⟩ := ht
    use cs, S0, t0
    constructor
    · cases e with
      | var x =>
        cases x with
        | free fx =>
          simp [resolve] at hr ⊢
          cases hres : h1 fx with
          | none => simp [hres] at hr
          | some v =>
            simp [hres] at hr
            have := hheap fx v hres
            simp [this, hr]
        | bound bx => cases bx
      | tabs _ _ _ => simp [resolve] at hr ⊢; exact hr
      | abs _ _ _ => simp [resolve] at hr
      | cabs _ _ _ => simp [resolve] at hr
      | pack _ _ => simp [resolve] at hr
      | unit => simp [resolve] at hr
      | unpack _ _ => simp [resolve] at hr
      | app _ _ => simp [resolve] at hr
      | tapp _ _ => simp [resolve] at hr
      | capp _ _ => simp [resolve] at hr
      | letin _ _ => simp [resolve] at hr
    · intro H' denot Hsub hdenot_proper himply
      have henv' : (env.extend_tvar denot).is_monotonic := by
        intro X
        cases X with
        | here =>
          simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
          intro C
          exact (hdenot_proper C).1
        | there X' =>
          simp [TypeEnv.extend_tvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
          exact henv X'
      apply hfun H' denot (Heap.subsumes_trans Hsub hheap) hdenot_proper himply
  | cpoly B T =>
    intro h1 h2 e hheap ht
    simp [Ty.shape_val_denot] at ht ⊢
    have ⟨cs, B0, t0, hr, hfun⟩ := ht
    use cs, B0, t0
    constructor
    · cases e with
      | var x =>
        cases x with
        | free fx =>
          simp [resolve] at hr ⊢
          cases hres : h1 fx with
          | none => simp [hres] at hr
          | some v =>
            simp [hres] at hr
            have := hheap fx v hres
            simp [this, hr]
        | bound bx => cases bx
      | cabs _ _ _ => simp [resolve] at hr ⊢; exact hr
      | abs _ _ _ => simp [resolve] at hr
      | tabs _ _ _ => simp [resolve] at hr
      | pack _ _ => simp [resolve] at hr
      | unit => simp [resolve] at hr
      | unpack _ _ => simp [resolve] at hr
      | app _ _ => simp [resolve] at hr
      | tapp _ _ => simp [resolve] at hr
      | capp _ _ => simp [resolve] at hr
      | letin _ _ => simp [resolve] at hr
    · intro H' A0 Hsub hA0
      apply hfun H' A0 (Heap.subsumes_trans Hsub hheap) hA0

def capt_val_denot_is_monotonic {env : TypeEnv s} {φ : HeapTopology}
  (henv : TypeEnv.is_monotonic env)
  (T : Ty .capt s) :
  (Ty.capt_val_denot env φ T).is_monotonic := by
  cases T with
  | capt C S =>
    simp [Ty.capt_val_denot]
    exact shape_val_denot_is_monotonic henv S (C.denot env φ)

def exi_val_denot_is_monotonic {env : TypeEnv s} {φ : HeapTopology}
  (henv : TypeEnv.is_monotonic env)
  (T : Ty .exi s) :
  (Ty.exi_val_denot env φ T).is_monotonic := by
  cases T with
  | typ T =>
    simp [Ty.exi_val_denot]
    exact capt_val_denot_is_monotonic henv T
  | exi T =>
    intro h1 h2 e hheap ht
    simp [Ty.exi_val_denot] at ht ⊢
    have ⟨A, hA⟩ := ht
    use A
    have henv' : (env.extend_cvar A).is_monotonic := by
      intro X
      cases X with
      | there X' =>
        simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar, TypeEnv.lookup]
        exact henv X'
    exact capt_val_denot_is_monotonic henv' T hheap hA

-- TODO: This proof needs to be rewritten to work with Memory instead of Heap.
-- The old proof used eval_monotonic which now has a different signature requiring
-- well-formedness proofs. A proper fix requires threading well-formedness through
-- the denotational semantics.
def capt_exp_denot_is_monotonic {env : TypeEnv s} {φ : HeapTopology}
  (henv : TypeEnv.is_monotonic env)
  (T : Ty .capt s) :
  (Ty.capt_exp_denot env φ T).is_monotonic := by
  sorry

-- TODO: Same as capt_exp_denot_is_monotonic - needs rewrite for Memory system.
def exi_exp_denot_is_monotonic {env : TypeEnv s} {φ : HeapTopology}
  (henv : TypeEnv.is_monotonic env)
  (T : Ty .exi s) :
  (Ty.exi_exp_denot env φ T).is_monotonic := by
  sorry

end

theorem env_typing_monotonic
  (ht : EnvTyping Γ env φ store1)
  (hstore : store2.subsumes store1) :
  EnvTyping Γ env φ store2 := by
  induction Γ with
  | empty =>
    cases env with
    | empty => constructor
  | push Γ k ih =>
    cases env with
    | extend env' info =>
      cases k with
      | var T =>
        cases info with
        | var n =>
          simp [EnvTyping] at ht ⊢
          have ⟨hval, heq, ht'⟩ := ht
          constructor
          · have henv := typed_env_is_monotonic ht'
            exact capt_val_denot_is_monotonic henv T hstore hval
          · constructor
            · exact heq
            · exact ih ht'
      | tvar S =>
        cases info with
        | tvar d =>
          simp [EnvTyping] at ht ⊢
          have ⟨hproper, himply, ht'⟩ := ht
          constructor
          · exact hproper
          · constructor
            · intro C
              apply Denot.imply_after_subsumes (himply C) hstore
            · exact ih ht'
      | cvar B =>
        cases info with
        | cvar access =>
          simp [EnvTyping] at ht ⊢
          have ⟨hsub, ht'⟩ := ht
          constructor
          · exact hsub
          · exact ih ht'

-- def SemSubtyp (Γ : Ctx s) (T1 T2 : Ty .shape s) : Prop :=
--   ∀ env H,
--     EnvTyping Γ env H ->
--     (Ty.shape_val_denot env T1).ImplyAfter H (Ty.shape_val_denot env T2)

-- theorem denot_implyat_lift
--   (himp : (Ty.shape_val_denot env T1).ImplyAfter H (Ty.shape_val_denot env T2)) :
--   (Ty.capt_exp_denot env (.capt C T1)).ImplyAfter H (Ty.capt_exp_denot env (.capt C T2)) := by
--   intro A
--   intro H' hsub e h1
--   simp [Ty.capt_exp_denot] at h1 ⊢
--   apply eval_post_monotonic_general _ h1
--   apply Hpost.entails_after_subsumes <;> try exact hsub
--   simp [Ty.capt_val_denot]
--   intro h'' hsub' e' he'
--   apply (himp (C.denot env)) h'' hsub' e' he'

end CC
