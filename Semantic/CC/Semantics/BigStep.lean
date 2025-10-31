import Semantic.CC.Syntax
import Semantic.CC.Substitution
import Semantic.CC.Semantics.Heap

namespace CC

def reachability_of_loc
  (m : Memory)
  (l : Nat) :
  CapabilitySet :=
  match m.lookup l with
  | some .capability => {l}
  | some (.val ⟨_, _, R⟩) => R
  | none => {}

def expand_captures
  (m : Memory)
  (cs : CaptureSet {}) :
  CapabilitySet :=
  match cs with
  | .empty => {}
  | .var (.free loc) => reachability_of_loc m loc
  | .union cs1 cs2 => expand_captures m cs1 ∪ expand_captures m cs2

def compute_reachability
  (m : Memory)
  (v : Exp {}) (hv : v.IsSimpleVal) :
  CapabilitySet :=
  match v with
  | .abs cs _ _ => expand_captures m cs
  | .tabs cs _ _ => expand_captures m cs
  | .cabs cs _ _ => expand_captures m cs
  | .unit => {}

theorem reachability_of_loc_monotonic
  {m1 m2 : Memory}
  (hsub : m2.subsumes m1)
  (l : Nat)
  (hex : m1.lookup l = some v) :
  reachability_of_loc m2 l = reachability_of_loc m1 l := by
  have m2_eq : m2.lookup l = some v := hsub l v hex
  simp only [reachability_of_loc, Memory.lookup] at hex m2_eq ⊢
  rw [hex, m2_eq]

/-- Expanding a capture set in a bigger memory yields the same result.
Proof by induction on cs. Requires all free locations in cs to exist in m1. -/
theorem expand_captures_monotonic
  {m1 m2 : Memory}
  (hsub : m2.subsumes m1)
  (cs : CaptureSet {})
  (hwf : CaptureSet.WfInHeap cs m1.heap) :
  expand_captures m2 cs = expand_captures m1 cs := by
  induction cs with
  | empty =>
    -- Base case: empty capture set expands to empty in any memory
    rfl
  | var x =>
    cases x with
    | bound x =>
      -- Impossible: no bound variables in empty signature
      cases x
    | free loc =>
      -- Variable case: use reachability_of_loc_monotonic
      simp [expand_captures]
      -- Extract existence proof from well-formedness
      cases hwf with
      | wf_var_free hex =>
        -- We have hex : m1.heap loc = some cell_val
        -- This is the same as m1.lookup loc = some cell_val
        exact reachability_of_loc_monotonic hsub loc hex
  | cvar C =>
    -- Impossible: no capability variables in empty signature
    cases C
  | union cs1 cs2 ih1 ih2 =>
    -- Union case: by induction on both components
    -- First, extract well-formedness for both components
    cases hwf with
    | wf_union hwf1 hwf2 =>
      simp [expand_captures, ih1 hwf1, ih2 hwf2]

/-- Computing reachability of a value in a bigger memory yields the same result.
Proof by cases on hv, using expand_captures_monotonic. -/
theorem compute_reachability_monotonic
  {m1 m2 : Memory}
  (hsub : m2.subsumes m1)
  (v : Exp {})
  (hv : v.IsSimpleVal)
  (hwf : Exp.WfInHeap v m1.heap) :
  compute_reachability m2 v hv = compute_reachability m1 v hv := by
  -- Case analysis on the structure of the simple value
  cases hv with
  | abs =>
    -- Case: v = .abs cs T e
    -- compute_reachability m v = expand_captures m cs
    simp [compute_reachability]
    -- Extract well-formedness of the capture set
    cases hwf with
    | wf_abs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | tabs =>
    -- Case: v = .tabs cs T e
    simp [compute_reachability]
    cases hwf with
    | wf_tabs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | cabs =>
    -- Case: v = .cabs cs cb e
    simp [compute_reachability]
    cases hwf with
    | wf_cabs hwf_cs _ _ =>
      exact expand_captures_monotonic hsub _ hwf_cs
  | unit =>
    -- Case: v = .unit
    -- Both memories yield empty capability set
    rfl

inductive Eval : CapabilitySet -> Memory -> Exp {} -> Mpost -> Prop where
| eval_val :
  (hv : Exp.IsVal v) ->
  (hQ : Q v m) ->
  Eval C m v Q
| eval_var :
  (hQ : Q (.var x) m) ->
  Eval C m (.var x) Q
| eval_apply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Eval C m (e.subst (Subst.openVar y)) Q ->
  Eval C m (.app (.free x) y) Q
| eval_invoke {m : Memory} {x : Nat} :
  x ∈ C ->
  m.lookup x = some .capability ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Q .unit m ->
  Eval C m (.app (.free x) (.free y)) Q
| eval_tapply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R⟩) ->
  Eval C m (e.subst (Subst.openTVar .top)) Q ->
  Eval C m (.tapp (.free x) S) Q
| eval_capply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R⟩) ->
  Eval C m (e.subst (Subst.openCVar CS)) Q ->
  Eval C m (.capp (.free x) CS) Q
| eval_letin {m : Memory} {Q1 : Mpost} :
  (hpred : Q1.is_monotonic) ->
  Eval C m e1 Q1 ->
  (h_val : ∀ {m1} {v : Exp {}},
    (m1.subsumes m) ->
    (hv : Exp.IsSimpleVal v) ->
    (hwf_v : Exp.WfInHeap v m1.heap) ->
    Q1 v m1 ->
    ∀ l'
      (hfresh : m1.lookup l' = none),
      Eval C
        (m1.extend_val l' ⟨v, hv, compute_reachability m1 v hv⟩ hwf_v hfresh)
        (e2.subst (Subst.openVar (.free l')))
        Q) ->
  (h_var : ∀ {m1} {x : Var .var {}},
    (m1.subsumes m) ->
    (hwf_x : x.WfInHeap m1.heap) ->
    Q1 (.var x) m1 ->
    Eval C m1 (e2.subst (Subst.openVar x)) Q) ->
  Eval C m (.letin e1 e2) Q
| eval_unpack {m : Memory} {Q1 : Mpost} :
  (hpred : Q1.is_monotonic) ->
  Eval C m e1 Q1 ->
  (h_val : ∀ {m1} {x : Var .var {}} {cs : CaptureSet {}},
    (m1.subsumes m) ->
    (hwf_x : x.WfInHeap m1.heap) ->
    (hwf_cs : cs.WfInHeap m1.heap) ->
    Q1 (.pack cs x) m1 ->
    Eval C m1 (e2.subst (Subst.unpack cs x)) Q) ->
  Eval C m (.unpack e1 e2) Q

theorem eval_monotonic {m1 m2 : Memory}
  (hpred : Q.is_monotonic)
  (hsub : m2.subsumes m1)
  (hwf : Exp.WfInHeap e m1.heap)
  (heval : Eval C m1 e Q) :
  Eval C m2 e Q := by
  induction heval generalizing m2
  case eval_val hv hQ =>
    apply Eval.eval_val hv
    apply hpred hwf hsub hQ
  case eval_var hQ =>
    apply Eval.eval_var
    apply hpred hwf hsub hQ
  case eval_apply hx _ ih =>
    -- Extract well-formedness of the application
    cases hwf with
    | wf_app hwf_x hwf_y =>
      apply Eval.eval_apply
      · exact hsub _ _ hx
      · apply ih hpred hsub
        -- Need: Exp.WfInHeap (e.subst (Subst.openVar y)) m1.heap
        -- Use Exp.wf_subst with Subst.wf_openVar
        apply Exp.wf_subst
        · -- Need: Exp.WfInHeap e m1.heap
          -- Get it from Memory.wf_lookup and inversion
          have hwf_abs := Memory.wf_lookup hx
          have ⟨_, _, hwf_e⟩ := Exp.wf_inv_abs hwf_abs
          exact hwf_e
        · -- Show: (Subst.openVar y).WfInHeap m1.heap
          apply Subst.wf_openVar
          exact hwf_y
  case eval_invoke hmem hx hy hQ =>
    apply Eval.eval_invoke
    · exact hmem
    · exact hsub _ _ hx
    · exact hsub _ _ hy
    · apply hpred
      · apply Exp.WfInHeap.wf_unit
      · exact hsub
      · exact hQ
  case eval_tapply hx _ ih =>
    apply Eval.eval_tapply
    · exact hsub _ _ hx
    · apply ih hpred hsub
      -- Need: Exp.WfInHeap (e.subst (Subst.openTVar .top)) m1.heap
      -- Use Exp.wf_subst with Subst.wf_openTVar
      apply Exp.wf_subst
      · -- Need: Exp.WfInHeap e m1.heap
        -- Get it from Memory.wf_lookup and inversion
        have hwf_tabs := Memory.wf_lookup hx
        have ⟨_, _, hwf_e⟩ := Exp.wf_inv_tabs hwf_tabs
        exact hwf_e
      · -- Show: (Subst.openTVar .top).WfInHeap m1.heap
        apply Subst.wf_openTVar
        apply Ty.WfInHeap.wf_top
  case eval_capply hx _ ih =>
    -- Extract well-formedness of the capability application
    cases hwf with
    | wf_capp hwf_x hwf_cs =>
      apply Eval.eval_capply
      · exact hsub _ _ hx
      · apply ih hpred hsub
        -- Need: Exp.WfInHeap (e.subst (Subst.openCVar CS)) m1.heap
        -- Use Exp.wf_subst with Subst.wf_openCVar
        apply Exp.wf_subst
        · -- Need: Exp.WfInHeap e m1.heap
          -- Get it from Memory.wf_lookup and inversion
          have hwf_cabs := Memory.wf_lookup hx
          have ⟨_, _, hwf_e⟩ := Exp.wf_inv_cabs hwf_cabs
          exact hwf_e
        · -- Show: (Subst.openCVar CS).WfInHeap m1.heap
          apply Subst.wf_openCVar
          exact hwf_cs
  case eval_letin Q1 hpred0 eval_e1 h_val_orig h_var_orig ih ih_val ih_var =>
    rename_i C_orig e1_orig Q_orig e2_orig m_orig
    -- Use inversion to extract well-formedness of subexpressions
    have ⟨hwf1, hwf2⟩ := Exp.wf_inv_letin hwf
    -- Apply IH for e1 with well-formedness
    have eval_e1' := ih hpred0 hsub hwf1
    apply Eval.eval_letin (Q1:=Q1) hpred0 eval_e1'
    case h_val =>
      intro m_ext' v hs_ext' hv hwf_v hq1 l' hfresh
      -- We have: m_ext'.subsumes m2 and m2.subsumes m_orig (the original memory)
      -- Therefore: m_ext'.subsumes m_orig
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      -- Now we can directly apply h_val_orig with all required arguments
      -- The key is that eval_letin now provides hwf_v: Exp.WfInHeap v m_ext'.heap
      exact h_val_orig hs_orig hv hwf_v hq1 l' hfresh
    case h_var =>
      intro m_ext' x hs_ext' hwf_x hq1
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      apply ih_var hs_orig hwf_x hq1 hpred
      · exact Memory.subsumes_refl _
      · -- Need: (e2_orig.subst (Subst.openVar x)).WfInHeap m_ext'.heap
        -- First, lift hwf2 to m_ext'.heap using monotonicity
        have hwf2_ext : Exp.WfInHeap e2_orig m_ext'.heap := Exp.wf_monotonic hs_orig hwf2
        -- Then apply substitution preservation
        apply Exp.wf_subst hwf2_ext
        apply Subst.wf_openVar hwf_x
  case eval_unpack Q1 hpred0 eval_e1 h_val_orig ih ih_val =>
    rename_i C_orig e1_orig Q_orig e2_orig m_orig
    -- Use inversion to extract well-formedness of subexpressions
    have ⟨hwf1, hwf2⟩ := Exp.wf_inv_unpack hwf
    -- Apply IH for e1 with well-formedness
    have eval_e1' := ih hpred0 hsub hwf1
    apply Eval.eval_unpack (Q1:=Q1) hpred0 eval_e1'
    -- The updated eval_unpack now provides both hwf_x and hwf_cs
    intro m_ext' x cs hs_ext' hwf_x hwf_cs hq1
    have hs_orig := Memory.subsumes_trans hs_ext' hsub
    apply ih_val hs_orig hwf_x hwf_cs hq1 hpred
    · exact Memory.subsumes_refl _
    · -- Need: (e2.subst (Subst.unpack cs x)).WfInHeap m_ext'.heap
      -- Lift hwf2 to m_ext'.heap using monotonicity
      have hwf2_ext : Exp.WfInHeap e2_orig m_ext'.heap := Exp.wf_monotonic hs_orig hwf2
      -- Apply substitution preservation
      apply Exp.wf_subst hwf2_ext
      -- Need: (Subst.unpack cs x).WfInHeap m_ext'.heap
      apply Subst.wf_unpack hwf_cs hwf_x

def Mpost.entails_at (Q1 : Mpost) (m : Memory) (Q2 : Mpost) : Prop :=
  ∀ e, Q1 e m -> Q2 e m

def Mpost.entails_after (Q1 : Mpost) (m : Memory) (Q2 : Mpost) : Prop :=
  ∀ m', m'.subsumes m -> Q1.entails_at m' Q2

lemma Mpost.entails_to_entails_after {Q1 Q2 : Mpost}
  (himp : Q1.entails Q2) :
  Q1.entails_after m Q2 := by
  intro m' hsub
  intro e hQ
  apply himp m' e hQ

theorem Mpost.entails_after_refl (Q : Mpost) (m : Memory) :
  Q.entails_after m Q := by
  intro m' _
  intro e hQ
  exact hQ

theorem Mpost.entails_after_subsumes
  (himp : Mpost.entails_after Q1 m Q2)
  (hsub : m'.subsumes m) :
  Q1.entails_after m' Q2 := by
  intro M mheap e
  apply himp M _
  apply Memory.subsumes_trans mheap hsub

theorem eval_post_monotonic_general {Q1 Q2 : Mpost}
  (himp : Q1.entails_after m Q2)
  (heval : Eval C m e Q1) :
  Eval C m e Q2 := by
  induction heval generalizing Q2
  case eval_val v Q M hv hQ =>
    apply Eval.eval_val hv
    apply himp M _ _ hQ
    apply Memory.subsumes_refl
  case eval_var Q1 M x hQ =>
    apply Eval.eval_var
    apply himp M _ _ hQ
    apply Memory.subsumes_refl
  case eval_apply hx _ ih =>
    apply Eval.eval_apply hx
    apply ih himp
  case eval_invoke hmem hx hy hQ =>
    apply Eval.eval_invoke hmem hx hy
    apply himp _ _ _ hQ
    apply Memory.subsumes_refl
  case eval_tapply hx _ ih =>
    apply Eval.eval_tapply hx
    apply ih himp
  case eval_capply hx _ ih =>
    apply Eval.eval_capply hx
    apply ih himp
  case eval_letin _ Q0 hpred he1 _ _ ih ih_val ih_var =>
    specialize ih (by apply Mpost.entails_after_refl)
    apply Eval.eval_letin (Q1:=Q0) hpred ih
    case h_val =>
      intro m1 v hs1 hv hwf_v hq1 l' hfresh
      apply ih_val hs1 hv hwf_v hq1 l' hfresh
      apply Mpost.entails_after_subsumes himp
      apply Memory.subsumes_trans (Memory.extend_val_subsumes _ _ _ hwf_v hfresh) hs1
    case h_var =>
      intro m1 x hs1 hwf_x hq1
      apply ih_var hs1 hwf_x hq1
      apply Mpost.entails_after_subsumes himp
      apply hs1
  case eval_unpack _ Q0 hpred he1 _ ih ih_val =>
    specialize ih (by apply Mpost.entails_after_refl)
    apply Eval.eval_unpack (Q1:=Q0) hpred ih
    intro m1 x cs hs1 hwf_x hwf_cs hq1
    apply ih_val hs1 hwf_x hwf_cs hq1
    apply Mpost.entails_after_subsumes himp
    apply hs1

theorem eval_post_monotonic {Q1 Q2 : Mpost}
  (himp : Q1.entails Q2)
  (heval : Eval C m e Q1) :
  Eval C m e Q2 := by
  apply eval_post_monotonic_general _ heval
  apply Mpost.entails_to_entails_after himp

theorem eval_capability_set_monotonic {A1 A2 : CapabilitySet}
  (heval : Eval A1 m e Q)
  (hsub : A1 ⊆ A2) :
  Eval A2 m e Q := sorry

end CC
