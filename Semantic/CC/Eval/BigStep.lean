import Semantic.CC.Syntax
import Semantic.CC.Substitution
import Semantic.CC.Eval.Heap

namespace CC

def reachability_of_loc
  (h : Heap)
  (l : Nat) :
  CapabilitySet :=
  match h l with
  | some .capability => {l}
  | some (.val ⟨_, _, R⟩) => R
  | none => {}

def expand_captures
  (h : Heap)
  (cs : CaptureSet {}) :
  CapabilitySet :=
  match cs with
  | .empty => {}
  | .var (.free loc) => reachability_of_loc h loc
  | .union cs1 cs2 => expand_captures h cs1 ∪ expand_captures h cs2

def compute_reachability
  (h : Heap)
  (v : Exp {}) (hv : v.IsSimpleVal) :
  CapabilitySet :=
  match v with
  | .abs cs _ _ => expand_captures h cs
  | .tabs cs _ _ => expand_captures h cs
  | .cabs cs _ _ => expand_captures h cs
  | .unit => {}

theorem reachability_of_loc_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (l : Nat)
  (hex : h1 l = some v) :
  reachability_of_loc h2 l = reachability_of_loc h1 l := by
  have h2_eq : h2 l = some v := hsub l v hex
  unfold reachability_of_loc
  rw [hex, h2_eq]

/-- Expanding a capture set in a bigger heap yields the same result.
Proof by induction on cs. Requires all free locations in cs to exist in h1. -/
theorem expand_captures_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (cs : CaptureSet {})
  (hwf : CaptureSet.WfInHeap cs h1) :
  expand_captures h2 cs = expand_captures h1 cs := by
  induction cs with
  | empty =>
    -- Base case: empty capture set expands to empty in any heap
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
        -- We have hex : h1 loc = some val
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

/-- Computing reachability of a value in a bigger heap yields the same result.
Proof by cases on hv, using expand_captures_monotonic. -/
theorem compute_reachability_monotonic
  {h1 h2 : Heap}
  (hsub : h2.subsumes h1)
  (v : Exp {})
  (hv : v.IsSimpleVal)
  (hwf : Exp.WfInHeap v h1) :
  compute_reachability h2 v hv = compute_reachability h1 v hv := by
  -- Case analysis on the structure of the simple value
  cases hv with
  | abs =>
    -- Case: v = .abs cs T e
    -- compute_reachability h v = expand_captures h cs
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
    -- Both heaps yield empty capability set
    rfl

inductive Eval : CapabilitySet -> Heap -> Exp {} -> Hpost -> Prop where
| eval_val :
  (hv : Exp.IsVal v) ->
  (hQ : Q v h) ->
  Eval C h v Q
| eval_var :
  (hQ : Q (.var x) h) ->
  Eval C h (.var x) Q
| eval_apply {h : Heap} {x : Nat} :
  h x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Eval C h (e.subst (Subst.openVar y)) Q ->
  Eval C h (.app (.free x) y) Q
| eval_invoke {h : Heap} {x : Nat} :
  x ∈ C ->
  h x = some .capability ->
  h y = some (.val ⟨.unit, hv, R⟩) ->
  Q .unit h ->
  Eval C h (.app (.free x) (.free y)) Q
| eval_tapply {h : Heap} {x : Nat} :
  h x = some (.val ⟨.tabs cs T0 e, hv, R⟩) ->
  Eval C h (e.subst (Subst.openTVar .top)) Q ->
  Eval C h (.tapp (.free x) S) Q
| eval_capply {h : Heap} {x : Nat} :
  h x = some (.val ⟨.cabs cs B0 e, hv, R⟩) ->
  Eval C h (e.subst (Subst.openCVar .empty)) Q ->
  Eval C h (.capp (.free x) CS) Q
| eval_letin {h : Heap} {Q1 : Hpost} :
  (hpred : Q1.is_monotonic) ->
  Eval C h e1 Q1 ->
  (h_val : ∀ {h1} {v : Exp {}},
    (h1.subsumes h) ->
    (hv : Exp.IsSimpleVal v) ->
    Q1 v h1 ->
    ∀ l', h1 l' = none ->
      Eval C
        (h1.extend l' ⟨v, hv, compute_reachability h v hv⟩)
        (e2.subst (Subst.openVar (.free l')))
        Q) ->
  (h_var : ∀ {h1} {x : Var .var {}},
    (h1.subsumes h) ->
    Q1 (.var x) h1 ->
    Eval C h1 (e2.subst (Subst.openVar x)) Q) ->
  Eval C h (.letin e1 e2) Q
| eval_unpack {h : Heap} {Q1 : Hpost} :
  (hpred : Q1.is_monotonic) ->
  Eval C h e1 Q1 ->
  (h_val : ∀ {h1} {x : Var .var {}} {cs : CaptureSet {}},
    (h1.subsumes h) ->
    Q1 (.pack cs x) h1 ->
    Eval C h1 (e2.subst (Subst.unpack cs x)) Q) ->
  Eval C h (.unpack e1 e2) Q

theorem eval_monotonic {h1 h2 : Heap}
  (hpred : Q.is_monotonic)
  (hsub : h2.subsumes h1)
  (heval : Eval C h1 e Q) :
  Eval C h2 e Q := by
  induction heval generalizing h2
  case eval_val hv hQ =>
    apply Eval.eval_val hv
    apply hpred hsub hQ
  case eval_var hQ =>
    apply Eval.eval_var
    apply hpred hsub hQ
  case eval_apply hx _ ih =>
    specialize ih hpred hsub
    apply Eval.eval_apply
    · apply hsub _ _ hx
    · assumption
  case eval_invoke hmem hx hy hQ =>
    apply Eval.eval_invoke
    · exact hmem
    · apply hsub _ _ hx
    · apply hsub _ _ hy
    · apply hpred <;> assumption
  case eval_tapply hx _ ih =>
    specialize ih hpred hsub
    apply Eval.eval_tapply
    · apply hsub _ _ hx
    · assumption
  case eval_capply hx _ ih =>
    specialize ih hpred hsub
    apply Eval.eval_capply
    · apply hsub _ _ hx
    · assumption
  case eval_letin Q1 hpred0 _ _ _ ih ih_val ih_var =>
    specialize ih hpred0 hsub
    apply Eval.eval_letin (Q1:=Q1) hpred0 ih
    case h_val =>
      intro h1 v hs1 hv hq1 l' hfresh
      -- h1.subsumes h2, h2.subsumes h1_original, so h1.subsumes h1_original
      have hs_orig := Heap.subsumes_trans hs1 hsub
      apply ih_val hs_orig hv hq1 l' hfresh hpred
      sorry --apply Heap.subsumes_refl
    case h_var =>
      intro h1 x hs1 hq1
      -- h1.subsumes h2, h2.subsumes h1_original, so h1.subsumes h1_original
      have hs_orig := Heap.subsumes_trans hs1 hsub
      apply ih_var hs_orig hq1 hpred
      apply Heap.subsumes_refl
  case eval_unpack Q1 hpred0 _ _ ih ih_val =>
    specialize ih hpred0 hsub
    apply Eval.eval_unpack (Q1:=Q1) hpred0 ih
    intro h1 x cs hs1 hq1
    -- h1.subsumes h2, h2.subsumes h1_original, so h1.subsumes h1_original
    have hs_orig := Heap.subsumes_trans hs1 hsub
    apply ih_val hs_orig hq1 hpred
    apply Heap.subsumes_refl

def Hpost.entails_at (Q1 : Hpost) (h : Heap) (Q2 : Hpost) : Prop :=
  ∀ e, Q1 e h -> Q2 e h

def Hpost.entails_after (Q1 : Hpost) (h : Heap) (Q2 : Hpost) : Prop :=
  ∀ h', h'.subsumes h -> Q1.entails_at h' Q2

lemma Hpost.entails_to_entails_after {Q1 Q2 : Hpost}
  (himp : Q1.entails Q2) :
  Q1.entails_after h Q2 := by
  intro h' hsub
  intro e hQ
  apply himp h' e hQ

theorem Hpost.entails_after_refl (Q : Hpost) (h : Heap) :
  Q.entails_after h Q := by
  intro h' _
  intro e hQ
  exact hQ

theorem Hpost.entails_after_subsumes
  (himp : Hpost.entails_after Q1 h Q2)
  (hsub : h'.subsumes h) :
  Q1.entails_after h' Q2 := by
  intro H hheap e
  apply himp H _
  apply Heap.subsumes_trans hheap hsub

theorem eval_post_monotonic_general {Q1 Q2 : Hpost}
  (himp : Q1.entails_after h Q2)
  (heval : Eval C h e Q1) :
  Eval C h e Q2 := by
  induction heval generalizing Q2
  case eval_val v Q H hv hQ =>
    apply Eval.eval_val hv
    apply himp H _ _ hQ
    apply Heap.subsumes_refl
  case eval_var Q1 H x hQ =>
    apply Eval.eval_var
    apply himp H _ _ hQ
    apply Heap.subsumes_refl
  case eval_apply hx _ ih =>
    apply Eval.eval_apply hx
    apply ih himp
  case eval_invoke hmem hx hy hQ =>
    apply Eval.eval_invoke hmem hx hy
    apply himp _ _ _ hQ
    apply Heap.subsumes_refl
  case eval_tapply hx _ ih =>
    apply Eval.eval_tapply hx
    apply ih himp
  case eval_capply hx _ ih =>
    apply Eval.eval_capply hx
    apply ih himp
  case eval_letin _ Q0 hpred he1 _ _ ih ih_val ih_var =>
    specialize ih (by apply Hpost.entails_after_refl)
    apply Eval.eval_letin (Q1:=Q0) hpred ih
    case h_val =>
      intro h1 v hs1 hv hq1 l' hfresh
      apply ih_val hs1 hv hq1 l' hfresh
      apply Hpost.entails_after_subsumes himp
      apply Heap.subsumes_trans (Heap.extend_subsumes hfresh) hs1
    case h_var =>
      intro h1 x hs1 hq1
      apply ih_var hs1 hq1
      apply Hpost.entails_after_subsumes himp
      apply hs1
  case eval_unpack _ Q0 hpred he1 _ ih ih_val =>
    specialize ih (by apply Hpost.entails_after_refl)
    apply Eval.eval_unpack (Q1:=Q0) hpred ih
    intro h1 x cs hs1 hq1
    apply ih_val hs1 hq1
    apply Hpost.entails_after_subsumes himp
    apply hs1

theorem eval_post_monotonic {Q1 Q2 : Hpost}
  (himp : Q1.entails Q2)
  (heval : Eval C h e Q1) :
  Eval C h e Q2 := by
  apply eval_post_monotonic_general _ heval
  apply Hpost.entails_to_entails_after himp

end CC
