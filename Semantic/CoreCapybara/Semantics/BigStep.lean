import Semantic.CoreCapybara.Syntax
import Semantic.CoreCapybara.Substitution
import Semantic.CoreCapybara.Semantics.Heap

namespace CoreCapybara

/-- Trace-observing memory postcondition: like `Mpost`, but the result
  predicate additionally observes the `Trace` of heap events that the
  evaluation produced. -/
def Tpost := Trace -> Exp {} -> Mprop

/-- Monotonicity of trace postconditions (in the memory, at a fixed trace). -/
def Tpost.is_monotonic (Q : Tpost) : Prop :=
  ∀ {t : Trace} {m1 m2 : Memory} {e},
    (hwf_e : e.WfInHeap m1.heap) ->
    m2.subsumes m1 ->
    Q t e m1 ->
    Q t e m2

def Tpost.is_bool_independent (Q : Tpost) : Prop :=
  ∀ {t : Trace} {m : Memory},
    Q t (.btrue) m <-> Q t (.bfalse) m

/-- Entailment between trace postconditions. -/
def Tpost.entails (Q1 Q2 : Tpost) : Prop :=
  ∀ t m e,
    Q1 t e m ->
    Q2 t e m

def Tpost.entails_refl (Q : Tpost) : Q.entails Q := by
  intros t m e hQ
  exact hQ

/-- Trace-instrumented big-step evaluation.

  `Eval m e Q` means: evaluating `e` from memory `m` produces some trace `t` of
  heap events, ending at a value and memory at which `Q t` holds.  Each heap
  effect is recorded in the trace handed to `Q`; the per-rule traces agree with
  `SmallStep.Step`. -/
inductive Eval : Memory -> Exp {} -> Tpost -> Prop where
| eval_pack :
  (hQ : Q [] (.pack cs x) m) ->
  Eval m (.pack cs x) Q
| eval_alloc {m : Memory} {x : Nat} {b : Bool} {hv R} :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  (h_post : ∀ l (hfresh : m.heap l = none),
    Q [.alloc l] (.pack (.var (.M .epsilon) (.free l)) (.free l)) (m.extend_mcell l b hfresh)) ->
  Eval m (.alloc (.free x)) Q
| eval_val :
  (hv : Exp.IsSimpleVal v) ->
  (hQ : Q [] v m) ->
  Eval m v Q
| eval_var :
  (hQ : Q [] (.var x) m) ->
  Eval m (.var x) Q
| eval_apply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Eval m (e.subst (Subst.openVar y)) Q ->
  Eval m (.app (.free x) y) Q
| eval_invoke {m : Memory} {x : Nat} :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Q [.access .epsilon x] .unit m ->
  Eval m (.app (.free x) (.free y)) Q
| eval_tapply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R⟩) ->
  Eval m (e.subst (Subst.openTVar .top)) Q ->
  Eval m (.tapp (.free x) S) Q
| eval_capply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R⟩) ->
  Eval m (e.subst (Subst.openCVar CS)) Q ->
  Eval m (.capp (.free x) CS) Q
| eval_wrap :
  Q [] (.boxed cs Ψ e) m ->
  Eval m (.boxed cs Ψ e) Q
| eval_unwrap {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩) ->
  Eval m e Q ->
  Eval m (.unwrap (.free x)) Q
| eval_letin {m : Memory} {Q1 : Tpost} :
  (hpred : Q1.is_monotonic) ->
  (hbool : Q1.is_bool_independent) ->
  Eval m e1 Q1 ->
  (h_nonstuck : ∀ {t1 : Trace} {m1 : Memory} {v : Exp {}},
    Q1 t1 v m1 ->
    v.IsSimpleAns ∧
    Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {t1 : Trace} {m1} {v : Exp {}},
    (m1.subsumes m) ->
    (hv : Exp.IsSimpleVal v) ->
    (hwf_v : Exp.WfInHeap v m1.heap) ->
    Q1 t1 v m1 ->
    ∀ l'
      (hfresh : m1.lookup l' = none),
      Eval
        (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩
          hwf_v rfl hfresh)
        (e2.subst (Subst.openVar (.free l')))
        (fun t2 => Q (t1 ++ t2))) ->
  (h_var : ∀ {t1 : Trace} {m1} {x : Var .var {}},
    (m1.subsumes m) ->
    (hwf_x : x.WfInHeap m1.heap) ->
    Q1 t1 (.var x) m1 ->
    Eval m1 (e2.subst (Subst.openVar x)) (fun t2 => Q (t1 ++ t2))) ->
  Eval m (.letin e1 e2) Q
| eval_unpack {m : Memory} {Q1 : Tpost} :
  (hpred : Q1.is_monotonic) ->
  (hbool : Q1.is_bool_independent) ->
  Eval m e1 Q1 ->
  (h_nonstuck : ∀ {t1 : Trace} {m1 : Memory} {v : Exp {}},
    Q1 t1 v m1 ->
    v.IsPack ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {t1 : Trace} {m1} {x : Var .var {}} {cs : CaptureSet {}},
    (m1.subsumes m) ->
    (hwf_x : x.WfInHeap m1.heap) ->
    (hwf_cs : cs.WfInHeap m1.heap) ->
    Q1 t1 (.pack cs x) m1 ->
    Eval m1 (e2.subst (Subst.unpack cs x)) (fun t2 => Q (t1 ++ t2))) ->
  Eval m (.unpack e1 e2) Q
| eval_read {m : Memory} {x : Nat} {b : Bool} :
  m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  Q [.access .ro y] (if b then .btrue else .bfalse) m ->
  Eval m (.read (.free x)) Q
| eval_write_true {m : Memory} {x y : Nat} :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Q [.access .epsilon x] .unit (m.update_mcell x true .live ⟨b0, hx⟩) ->
  Eval m (.write (.free x) (.free y)) Q
| eval_write_false {m : Memory} {x y : Nat} :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Q [.access .epsilon x] .unit (m.update_mcell x false .live ⟨b0, hx⟩) ->
  Eval m (.write (.free x) (.free y)) Q
| eval_drop :
  (hx : m.lookup x = some (.capability (.mcell b .live))) ->
  Q [.dealloc x] .unit (m.drop_mcell x ⟨b, hx⟩) ->
  Eval m (.drop (.free x)) Q
| eval_cond {m : Memory} {x : Var .var {}} :
  (hres : resolve m.heap (.var x) = some .btrue ∨ resolve m.heap (.var x) = some .bfalse) ->
  (h_true : resolve m.heap (.var x) = some .btrue → Eval m e2 Q) ->
  (h_false : resolve m.heap (.var x) = some .bfalse → Eval m e3 Q) ->
  Eval m (.cond x e2 e3) Q
| eval_par :
  Eval m e1 Q ->
  Eval m e2 Q ->
  Eval m (.par e1 e2) Q

/-- `Eval` on a variable does not change memory and emits no events: the only
    rule producing `Eval m (.var x) Q` is `eval_var`. -/
theorem Eval.var_inv {m : Memory} {x : Var .var {}} {Q : Tpost}
    (heval : Eval m (.var x) Q) : Q [] (.var x) m := by
  cases heval with
  | eval_val hv _ => cases hv
  | eval_var hQ => exact hQ

/-- Trace-footprint liveness condition for memory subsumption.

  `SubsumeOk m1 t m2` holds when every mutable cell that is **live in `m1`** and
  **touched by the trace `t`** — read or written (`access`) or dropped
  (`dealloc`) — remains **live in `m2`**.  An `alloc` refers to a fresh location,
  so it imposes no constraint. -/
def Memory.SubsumeOk (m1 : Memory) (t : Trace) (m2 : Memory) : Prop :=
  ∀ l b,
    m1.lookup l = some (.capability (.mcell b .live)) ->
    ((∃ mu, TraceItem.access mu l ∈ t) ∨ TraceItem.dealloc l ∈ t) ->
    ∃ b', m2.lookup l = some (.capability (.mcell b' .live))

/-- Answer existence: every `Eval m e Q` is witnessed by an actual answer — a
  trace `t`, an answer value `e'`, and a memory `m' ⊒ m` with `Q t e' m'`. -/
theorem eval_exists_answer (heval : Eval m e Q) :
  ∃ t e' m', e'.IsAns ∧ m'.subsumes m ∧ Q t e' m' := by
  induction heval with
  | eval_pack hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_val Exp.IsVal.pack, Memory.subsumes_refl _, hQ⟩
  | eval_alloc _ h_post =>
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact ⟨_, _, _, Exp.IsAns.is_val Exp.IsVal.pack,
           Memory.extend_mcell_subsumes _ _ _ hfresh, h_post l hfresh⟩
  | eval_val hv hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_val (by cases hv <;> constructor),
           Memory.subsumes_refl _, hQ⟩
  | eval_var hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_var, Memory.subsumes_refl _, hQ⟩
  | eval_apply _ _ ih => exact ih
  | eval_invoke _ _ hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_val Exp.IsVal.unit, Memory.subsumes_refl _, hQ⟩
  | eval_tapply _ _ ih => exact ih
  | eval_capply _ _ ih => exact ih
  | eval_wrap hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_val Exp.IsVal.boxed, Memory.subsumes_refl _, hQ⟩
  | eval_unwrap _ _ ih => exact ih
  | eval_letin hpred hbool eval_e1 h_nonstuck h_val h_var ih_e1 ih_val ih_var =>
    obtain ⟨t1, v1, m1', hans1, hsub1, hq1⟩ := ih_e1
    obtain ⟨hsa, hwf1⟩ := h_nonstuck hq1
    cases hsa with
    | is_simple_val hv =>
      obtain ⟨l', hfresh⟩ := Memory.exists_fresh m1'
      obtain ⟨t2, v2, m2', hans2, hsub2, hq2⟩ := ih_val hsub1 hv hwf1 hq1 l' hfresh
      exact ⟨t1 ++ t2, v2, m2', hans2,
             Memory.subsumes_trans hsub2
               (Memory.subsumes_trans
                 (Memory.extend_val_subsumes _ _ _ hwf1 rfl hfresh) hsub1), hq2⟩
    | is_var =>
      cases hwf1 with
      | wf_var hwf_x =>
        obtain ⟨t2, v2, m2', hans2, hsub2, hq2⟩ := ih_var hsub1 hwf_x hq1
        exact ⟨t1 ++ t2, v2, m2', hans2, Memory.subsumes_trans hsub2 hsub1, hq2⟩
  | eval_unpack hpred hbool eval_e1 h_nonstuck h_val ih_e1 ih_val =>
    obtain ⟨t1, v1, m1', hans1, hsub1, hq1⟩ := ih_e1
    obtain ⟨hpack, hwf1⟩ := h_nonstuck hq1
    cases hpack with
    | pack =>
      cases hwf1 with
      | wf_pack hwf_cs hwf_x =>
        obtain ⟨t2, v2, m2', hans2, hsub2, hq2⟩ := ih_val hsub1 hwf_x hwf_cs hq1
        exact ⟨t1 ++ t2, v2, m2', hans2, Memory.subsumes_trans hsub2 hsub1, hq2⟩
  | eval_read _ _ hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_val (by split <;> constructor),
           Memory.subsumes_refl _, hQ⟩
  | eval_write_true hx _ hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_val Exp.IsVal.unit,
           Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩, hQ⟩
  | eval_write_false hx _ hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_val Exp.IsVal.unit,
           Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩, hQ⟩
  | eval_drop hx hQ =>
    exact ⟨_, _, _, Exp.IsAns.is_val Exp.IsVal.unit,
           Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩, hQ⟩
  | eval_cond hres _ _ ih_true ih_false =>
    cases hres with
    | inl hbtrue => exact ih_true hbtrue
    | inr hbfalse => exact ih_false hbfalse
  | eval_par _ _ ih1 _ => exact ih1

/-- `SubsumeOk` is antitone in the trace: preserving the cells touched by a
  longer trace `t1 ++ t2` in particular preserves those touched by `t1`. -/
theorem Memory.SubsumeOk.mono_append {m1 m2 : Memory} {t1 t2 : Trace}
  (h : Memory.SubsumeOk m1 (t1 ++ t2) m2) : Memory.SubsumeOk m1 t1 m2 := by
  intro l b hlive htouched
  refine h l b hlive ?_
  rcases htouched with ⟨mu, hmem⟩ | hmem
  · exact Or.inl ⟨mu, List.mem_append_left _ hmem⟩
  · exact Or.inr (List.mem_append_left _ hmem)

/-- Memory-subsumption monotonicity of `Eval`.

  The side condition `hok` carries the trace-footprint liveness: for every
  `Q`-result whose memory subsumes the source `m1`, the cells its trace touches
  that are live in `m1` remain live in `m2`. -/
theorem eval_monotonic {m1 m2 : Memory}
  (hpred : Q.is_monotonic)
  (hbool : Q.is_bool_independent)
  (hsub : m2.subsumes m1)
  (hok : ∀ t v m, m.subsumes m1 -> Q t v m -> Memory.SubsumeOk m1 t m2)
  (hwf : Exp.WfInHeap e m1.heap)
  (heval : Eval m1 e Q) :
  Eval m2 e Q := by
  induction heval generalizing m2
  case eval_pack hQ =>
    cases hwf with
    | wf_pack hwf_cs hwf_x =>
      exact Eval.eval_pack (hpred (Exp.WfInHeap.wf_pack hwf_cs hwf_x) hsub hQ)
  case eval_alloc hlookup h_post =>
    rename_i m_orig _ b _ _
    obtain ⟨v', hlookup', hsub_v⟩ := hsub _ _ hlookup
    simp only [Cell.subsumes] at hsub_v
    subst hsub_v
    apply Eval.eval_alloc hlookup'
    intro l hfresh2
    have hfresh1 : m_orig.heap l = none := by
      cases h : m_orig.heap l with
      | none => rfl
      | some v =>
        obtain ⟨_, hlookup_v, _⟩ := hsub _ _ h
        rw [hlookup_v] at hfresh2
        cases hfresh2
    have hheap_l : (m_orig.heap.extend_mcell l b) l = some (.capability (.mcell b .live)) := by
      unfold Heap.extend_mcell; rw [if_pos rfl]
    apply hpred ?_ ?_ (h_post l hfresh1)
    · exact Exp.WfInHeap.wf_pack
        (CaptureSet.WfInHeap.wf_var_free hheap_l)
        (Var.WfInHeap.wf_free hheap_l)
    · exact Memory.extend_mcell_subsumes_compat _ _ hfresh1 hfresh2 hsub
  case eval_val hv hQ =>
    apply Eval.eval_val hv
    apply hpred hwf hsub hQ
  case eval_var hQ =>
    apply Eval.eval_var
    apply hpred hwf hsub hQ
  case eval_apply hx _ ih =>
    cases hwf with
    | wf_app hwf_x hwf_y =>
      obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
      simp only [Cell.subsumes] at hsub_v
      subst hsub_v
      apply Eval.eval_apply
      · exact hx2
      · apply ih hpred hbool hsub hok (by
          apply Exp.wf_subst
          · have hwf_abs := Memory.wf_lookup hx
            have ⟨_, _, hwf_e⟩ := Exp.wf_inv_abs hwf_abs
            exact hwf_e
          · apply Subst.wf_openVar
            exact hwf_y)
  case eval_invoke hx hy hQ =>
    obtain ⟨v'x, hx2, hsub_vx⟩ := hsub _ _ hx
    obtain ⟨v'y, hy2, hsub_vy⟩ := hsub _ _ hy
    simp only [Cell.subsumes] at hsub_vx
    subst hsub_vx
    simp only [Cell.subsumes] at hsub_vy
    subst hsub_vy
    apply Eval.eval_invoke hx2 hy2
    apply hpred
    · apply Exp.WfInHeap.wf_unit
    · exact hsub
    · exact hQ
  case eval_tapply hx _ ih =>
    obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
    simp only [Cell.subsumes] at hsub_v
    subst hsub_v
    apply Eval.eval_tapply
    · exact hx2
    · apply ih hpred hbool hsub hok (by
        apply Exp.wf_subst
        · have hwf_tabs := Memory.wf_lookup hx
          have ⟨_, _, hwf_e⟩ := Exp.wf_inv_tabs hwf_tabs
          exact hwf_e
        · apply Subst.wf_openTVar
          apply Ty.WfInHeap.wf_top)
  case eval_capply hx _ ih =>
    cases hwf with
    | wf_capp hwf_x hwf_cs =>
      obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
      simp only [Cell.subsumes] at hsub_v
      subst hsub_v
      apply Eval.eval_capply
      · exact hx2
      · apply ih hpred hbool hsub hok (by
          apply Exp.wf_subst
          · have hwf_cabs := Memory.wf_lookup hx
            have ⟨_, _, hwf_e⟩ := Exp.wf_inv_cabs hwf_cabs
            exact hwf_e
          · apply Subst.wf_openCVar
            exact hwf_cs)
  case eval_wrap hQ =>
    exact Eval.eval_wrap (hpred hwf hsub hQ)
  case eval_unwrap hx _ ih =>
    cases hwf with
    | wf_unwrap _ =>
      obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
      simp only [Cell.subsumes] at hsub_v
      subst hsub_v
      apply Eval.eval_unwrap hx2
      apply ih hpred hbool hsub hok
      have hwf_boxed := Memory.wf_lookup hx
      cases hwf_boxed with
      | wf_boxed _ _ hwf_e =>
        exact hwf_e
  case eval_letin Q1 hpred0 hbool0 eval_e1 h_nonstuck_orig h_val_orig h_var_orig ih _ _ =>
    have ⟨hwf1, _hwf2⟩ := Exp.wf_inv_letin hwf
    -- Specialise `hok` to `e1`'s postcondition `Q1`: run the continuation to an
    -- answer, apply `hok` to that `Q`-result, and restrict back to the prefix.
    have eval_e1' := ih hpred0 hbool0 hsub (by
      intro t v m hmsub hq1
      obtain ⟨hsa, hwf_v⟩ := h_nonstuck_orig hq1
      cases hsa with
      | is_simple_val hv =>
        obtain ⟨l', hfresh⟩ := Memory.exists_fresh m
        obtain ⟨t2, v', m', _, hsub', hq'⟩ :=
          eval_exists_answer (h_val_orig hmsub hv hwf_v hq1 l' hfresh)
        exact Memory.SubsumeOk.mono_append
          (hok (t ++ t2) v' m'
            (Memory.subsumes_trans hsub'
              (Memory.subsumes_trans (Memory.extend_val_subsumes _ _ _ hwf_v rfl hfresh) hmsub))
            hq')
      | is_var =>
        cases hwf_v with
        | wf_var hwf_x =>
          obtain ⟨t2, v', m', _, hsub', hq'⟩ :=
            eval_exists_answer (h_var_orig hmsub hwf_x hq1)
          exact Memory.SubsumeOk.mono_append
            (hok (t ++ t2) v' m' (Memory.subsumes_trans hsub' hmsub) hq')) hwf1
    apply Eval.eval_letin (Q1:=Q1) hpred0 hbool0 eval_e1'
    case h_nonstuck =>
      intro t1 m1 v hQ_orig
      exact h_nonstuck_orig hQ_orig
    case h_val =>
      intro t1 m_ext' v hs_ext' hv hwf_v hq1 l' hfresh
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      exact h_val_orig hs_orig hv hwf_v hq1 l' hfresh
    case h_var =>
      intro t1 m_ext' x hs_ext' hwf_x hq1
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      exact h_var_orig hs_orig hwf_x hq1
  case eval_unpack Q1 hpred0 hbool0 eval_e1 h_nonstuck_orig h_val_orig ih _ =>
    have ⟨hwf1, _hwf2⟩ := Exp.wf_inv_unpack hwf
    -- Specialise `hok` to `Q1` by running the unpacked body to an answer and
    -- restricting along the prefix.
    have eval_e1' := ih hpred0 hbool0 hsub (by
      intro t v m hmsub hq1
      obtain ⟨hpack, hwf_v⟩ := h_nonstuck_orig hq1
      cases hpack with
      | pack =>
        cases hwf_v with
        | wf_pack hwf_cs hwf_x =>
          obtain ⟨t2, v', m', _, hsub', hq'⟩ :=
            eval_exists_answer (h_val_orig hmsub hwf_x hwf_cs hq1)
          exact Memory.SubsumeOk.mono_append
            (hok (t ++ t2) v' m' (Memory.subsumes_trans hsub' hmsub) hq')) hwf1
    apply Eval.eval_unpack (Q1:=Q1) hpred0 hbool0 eval_e1'
    case h_nonstuck =>
      intro t1 m1 v hQ_orig
      exact h_nonstuck_orig hQ_orig
    case h_val =>
      intro t1 m_ext' x cs hs_ext' hwf_x hwf_cs hq1
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      exact h_val_orig hs_orig hwf_x hwf_cs hq1
  case eval_read hmem hx hQ =>
    rename_i b
    obtain ⟨cx, hx2, hsub_x⟩ := hsub _ _ hmem
    simp only [Cell.subsumes] at hsub_x
    subst hsub_x
    obtain ⟨b', hy2⟩ := (hok _ _ _ (Memory.subsumes_refl _) hQ) _ _ hx
      (Or.inl ⟨.ro, List.mem_singleton.mpr rfl⟩)
    apply Eval.eval_read hx2 hy2
    by_cases hb : b
    · subst hb
      have hQ_true := by simpa using hQ
      by_cases hb' : b' = true
      · subst b'
        simpa using hpred (by constructor) hsub hQ_true
      · have hb'_false : b' = false := by simpa using hb'
        subst b'
        have hQ_true_m2 := hpred (by constructor) hsub hQ_true
        have hQ_false_m2 := hbool.mp hQ_true_m2
        simpa using hQ_false_m2
    · have hb_false : b = false := by simpa using hb
      subst b
      have hQ_false := by simpa using hQ
      by_cases hb' : b' = true
      · subst b'
        have hQ_false_m2 := hpred (by constructor) hsub hQ_false
        have hQ_true_m2 := hbool.mpr hQ_false_m2
        simpa using hQ_true_m2
      · have hb'_false : b' = false := by simpa using hb'
        subst b'
        simpa using hpred (by constructor) hsub hQ_false
  case eval_write_true hx hy hQ =>
    obtain ⟨cy, hy2, hsub_y⟩ := hsub _ _ hy
    simp only [Cell.subsumes] at hsub_y
    subst hsub_y
    obtain ⟨b0', hx2⟩ := (hok _ _ _ (Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩) hQ) _ _ hx
      (Or.inl ⟨.epsilon, List.mem_singleton.mpr rfl⟩)
    apply Eval.eval_write_true (hx := hx2) hy2
    apply hpred
    · constructor
    · exact Memory.update_mcell_subsumes_compat _ _ _ (Exists.intro _ hx) (Exists.intro _ hx2) hsub
    · exact hQ
  case eval_write_false hx hy hQ =>
    obtain ⟨cy, hy2, hsub_y⟩ := hsub _ _ hy
    simp only [Cell.subsumes] at hsub_y
    subst hsub_y
    obtain ⟨b0', hx2⟩ := (hok _ _ _ (Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩) hQ) _ _ hx
      (Or.inl ⟨.epsilon, List.mem_singleton.mpr rfl⟩)
    apply Eval.eval_write_false (hx := hx2) hy2
    apply hpred
    · constructor
    · exact Memory.update_mcell_subsumes_compat _ _ _ (Exists.intro _ hx) (Exists.intro _ hx2) hsub
    · exact hQ
  case eval_drop hx hQ =>
    obtain ⟨b', hx2⟩ := (hok _ _ _ (Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩) hQ) _ _ hx
      (Or.inr (List.mem_singleton.mpr rfl))
    apply Eval.eval_drop hx2
    apply hpred
    · constructor
    · exact Memory.drop_mcell_subsumes_compat _ ⟨_, hx⟩ ⟨_, hx2⟩ hsub
    · exact hQ
  case eval_cond x hres h_true h_false ih_true ih_false =>
    rename_i _ _ _ m_orig
    have ⟨hwf_x, hwf2, hwf3⟩ := Exp.wf_inv_cond hwf
    have hres' :
        resolve m2.heap (.var x) = some .btrue ∨ resolve m2.heap (.var x) = some .bfalse := by
      cases hres with
      | inl h => exact .inl (resolve_monotonic hsub h)
      | inr h => exact .inr (resolve_monotonic hsub h)
    apply Eval.eval_cond hres'
    · intro hres_m2_true
      have hres_orig : resolve m_orig.heap (.var x) = some .btrue := by
        cases hres with
        | inl h => exact h
        | inr h =>
          have := resolve_monotonic hsub h
          rw [this] at hres_m2_true; cases hres_m2_true
      exact ih_true hres_orig hpred hbool hsub hok hwf2
    · intro hres_m2_false
      have hres_orig : resolve m_orig.heap (.var x) = some .bfalse := by
        cases hres with
        | inl h =>
          have := resolve_monotonic hsub h
          rw [this] at hres_m2_false; cases hres_m2_false
        | inr h => exact h
      exact ih_false hres_orig hpred hbool hsub hok hwf3
  case eval_par ih1 ih2 =>
    cases hwf with
    | wf_par hwf1 hwf2 =>
      exact Eval.eval_par
        (ih1 hpred hbool hsub hok hwf1)
        (ih2 hpred hbool hsub hok hwf2)

-- `Mpost`-level entailment-after machinery.
def Mpost.entails_at (Q1 : Mpost) (m : Memory) (Q2 : Mpost) : Prop :=
  ∀ e, Q1 e m -> Q2 e m

def Mpost.entails_after (Q1 : Mpost) (m : Memory) (Q2 : Mpost) : Prop :=
  ∀ m', m'.subsumes m -> Q1.entails_at m' Q2

lemma Mpost.entails_to_entails_after {Q1 Q2 : Mpost}
  (himp : Q1.entails Q2) :
  Q1.entails_after m Q2 := by
  intro m' hsub e hQ
  apply himp m' e hQ

theorem Mpost.entails_after_refl (Q : Mpost) (m : Memory) :
  Q.entails_after m Q := by
  intro m' _ e hQ
  exact hQ

theorem Mpost.entails_after_subsumes
  (himp : Mpost.entails_after Q1 m Q2)
  (hsub : m'.subsumes m) :
  Q1.entails_after m' Q2 := by
  intro M mheap e
  exact himp M (Memory.subsumes_trans mheap hsub) e

-- Trace-aware analogues, used by the trace-based `Eval`.
def Tpost.entails_at (Q1 : Tpost) (m : Memory) (Q2 : Tpost) : Prop :=
  ∀ t e, Q1 t e m -> Q2 t e m

def Tpost.entails_after (Q1 : Tpost) (m : Memory) (Q2 : Tpost) : Prop :=
  ∀ m', m'.subsumes m -> Q1.entails_at m' Q2

lemma Tpost.entails_to_entails_after {Q1 Q2 : Tpost}
  (himp : Q1.entails Q2) :
  Q1.entails_after m Q2 := by
  intro m' hsub t e hQ
  apply himp t m' e hQ

theorem Tpost.entails_after_refl (Q : Tpost) (m : Memory) :
  Q.entails_after m Q := by
  intro m' _ t e hQ
  exact hQ

theorem Tpost.entails_after_subsumes
  (himp : Tpost.entails_after Q1 m Q2)
  (hsub : m'.subsumes m) :
  Q1.entails_after m' Q2 := by
  intro M mheap t e
  exact himp M (Memory.subsumes_trans mheap hsub) t e

/-- Shift an `entails_after` past a fixed trace prefix `t1`.  Used to push a
    postcondition refinement through the `letin`/`unpack` continuation, whose
    postcondition is the outer `Q` shifted by the prefix produced by `e1`. -/
theorem Tpost.entails_after_shift {Q1 Q2 : Tpost} {m m' : Memory} {t1 : Trace}
  (himp : Q1.entails_after m Q2) (hsub : m'.subsumes m) :
  Tpost.entails_after (fun t2 => Q1 (t1 ++ t2)) m' (fun t2 => Q2 (t1 ++ t2)) := by
  intro M mheap t e hq
  exact himp M (Memory.subsumes_trans mheap hsub) (t1 ++ t) e hq

theorem eval_post_monotonic_general {Q1 Q2 : Tpost}
  (himp : Q1.entails_after m Q2)
  (heval : Eval m e Q1) :
  Eval m e Q2 := by
  induction heval generalizing Q2
  case eval_pack hQ =>
    exact Eval.eval_pack (himp _ (Memory.subsumes_refl _) _ _ hQ)
  case eval_alloc hlookup h_post =>
    apply Eval.eval_alloc hlookup
    intro l hfresh
    exact himp _ (Memory.extend_mcell_subsumes _ _ _ hfresh) _ _ (h_post l hfresh)
  case eval_val hv hQ =>
    exact Eval.eval_val hv (himp _ (Memory.subsumes_refl _) _ _ hQ)
  case eval_var hQ =>
    exact Eval.eval_var (himp _ (Memory.subsumes_refl _) _ _ hQ)
  case eval_apply hx _ ih =>
    exact Eval.eval_apply hx (ih himp)
  case eval_invoke hx hy hQ =>
    exact Eval.eval_invoke hx hy (himp _ (Memory.subsumes_refl _) _ _ hQ)
  case eval_tapply hx _ ih =>
    exact Eval.eval_tapply hx (ih himp)
  case eval_capply hx _ ih =>
    exact Eval.eval_capply hx (ih himp)
  case eval_wrap hQ =>
    exact Eval.eval_wrap (himp _ (Memory.subsumes_refl _) _ _ hQ)
  case eval_unwrap hx _ ih =>
    exact Eval.eval_unwrap hx (ih himp)
  case eval_letin _ Q0 hpred hbool0 he1 h_nonstuck h_val h_var ih ih_val ih_var =>
    specialize ih (by apply Tpost.entails_after_refl)
    apply Eval.eval_letin (Q1:=Q0) hpred hbool0 ih
    case h_nonstuck =>
      intro t1 m1 v hQ0
      exact h_nonstuck hQ0
    case h_val =>
      intro t1 m1 v hs1 hv hwf_v hq1 l' hfresh
      apply ih_val hs1 hv hwf_v hq1 l' hfresh
      exact Tpost.entails_after_shift himp
        (Memory.subsumes_trans (Memory.extend_val_subsumes _ _ _ hwf_v rfl hfresh) hs1)
    case h_var =>
      intro t1 m1 x hs1 hwf_x hq1
      apply ih_var hs1 hwf_x hq1
      exact Tpost.entails_after_shift himp hs1
  case eval_unpack _ Q0 hpred hbool0 he1 h_nonstuck h_val ih ih_val =>
    specialize ih (by apply Tpost.entails_after_refl)
    apply Eval.eval_unpack (Q1:=Q0) hpred hbool0 ih
    case h_nonstuck =>
      intro t1 m1 v hQ0
      exact h_nonstuck hQ0
    case h_val =>
      intro t1 m1 x cs hs1 hwf_x hwf_cs hq1
      apply ih_val hs1 hwf_x hwf_cs hq1
      exact Tpost.entails_after_shift himp hs1
  case eval_read hmem hx hQ =>
    exact Eval.eval_read hmem hx (himp _ (Memory.subsumes_refl _) _ _ hQ)
  case eval_write_true hx hy hQ =>
    apply Eval.eval_write_true hx hy
    apply himp _ _ _ _ hQ
    apply Memory.update_mcell_subsumes
  case eval_write_false hx hy hQ =>
    apply Eval.eval_write_false hx hy
    apply himp _ _ _ _ hQ
    apply Memory.update_mcell_subsumes
  case eval_drop hx hQ =>
    apply Eval.eval_drop hx
    apply himp _ _ _ _ hQ
    apply Memory.drop_mcell_subsumes
  case eval_cond hres h_true h_false ih_true ih_false =>
    apply Eval.eval_cond hres
    · intro hres_true
      exact ih_true hres_true himp
    · intro hres_false
      exact ih_false hres_false himp
  case eval_par ih1 ih2 =>
    exact Eval.eval_par (ih1 himp) (ih2 himp)

theorem eval_post_monotonic {Q1 Q2 : Tpost}
  (himp : Q1.entails Q2)
  (heval : Eval m e Q1) :
  Eval m e Q2 :=
  eval_post_monotonic_general (Tpost.entails_to_entails_after himp) heval

/-- Coverage in `C.to_drop` forces the mode to be `.drop`: `to_drop` rewrites
    every cap mode to `.drop`, and `.access _` is incomparable with `.drop`
    under `CapMode.Le`. -/
theorem CapabilitySet.covers_to_drop_imp_drop {C : CapabilitySet} {mu : CapMode} {l : Nat}
    (h : CapabilitySet.covers mu l C.to_drop) : mu = .drop := by
  induction C with
  | empty =>
    simp only [CapabilitySet.to_drop] at h
    cases h
  | cap m' l' =>
    simp only [CapabilitySet.to_drop] at h
    cases h with
    | here hle => cases hle; rfl
  | union C1 C2 ih1 ih2 =>
    simp only [CapabilitySet.to_drop] at h
    cases h with
    | left h' => exact ih1 h'
    | right h' => exact ih2 h'

end CoreCapybara
