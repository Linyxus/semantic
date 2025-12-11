import Semantic.Capybara.Syntax
import Semantic.Capybara.Substitution
import Semantic.Capybara.Semantics.Heap

namespace Capybara

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
  C.covers .epsilon x ->
  m.lookup x = some (.capability .basic) ->
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
  (hbool : Q1.is_bool_independent) ->
  Eval C m e1 Q1 ->
  (h_nonstuck : ∀ {m1 : Memory} {v : Exp {}},
    Q1 v m1 ->
    v.IsSimpleAns ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {m1} {v : Exp {}},
    (m1.subsumes m) ->
    (hv : Exp.IsSimpleVal v) ->
    (hwf_v : Exp.WfInHeap v m1.heap) ->
    Q1 v m1 ->
    ∀ l'
      (hfresh : m1.lookup l' = none),
      Eval C
        (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩
          hwf_v rfl hfresh)
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
  (hbool : Q1.is_bool_independent) ->
  Eval C m e1 Q1 ->
  (h_nonstuck : ∀ {m1 : Memory} {v : Exp {}},
    Q1 v m1 ->
    v.IsPack ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {m1} {x : Var .var {}} {cs : CaptureSet {}},
    (m1.subsumes m) ->
    (hwf_x : x.WfInHeap m1.heap) ->
    (hwf_cs : cs.WfInHeap m1.heap) ->
    Q1 (.pack cs x) m1 ->
    Eval C m1 (e2.subst (Subst.unpack cs x)) Q) ->
  Eval C m (.unpack e1 e2) Q
| eval_read {m : Memory} {x : Nat} {b : Bool} :
  C.covers .ro y ->
  m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩) ->
  m.lookup y = some (.capability (.mcell b)) ->
  Q (if b then .btrue else .bfalse) m ->
  Eval C m (.read (.free x)) Q
| eval_write_true {m : Memory} {x y : Nat} :
  C.covers .epsilon x ->
  (hx : m.lookup x = some (.capability (.mcell b0))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Q .unit (m.update_mcell x true ⟨b0, hx⟩) ->
  Eval C m (.write (.free x) (.free y)) Q
| eval_write_false {m : Memory} {x y : Nat} :
  C.covers .epsilon x ->
  (hx : m.lookup x = some (.capability (.mcell b0))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Q .unit (m.update_mcell x false ⟨b0, hx⟩) ->
  Eval C m (.write (.free x) (.free y)) Q
| eval_cond {m : Memory} {Q1 : Mpost} :
  (hpred : Q1.is_monotonic) ->
  (hbool : Q1.is_bool_independent) ->
  Eval C m (.var x) Q1 ->
  (h_nonstuck : ∀ {m1 : Memory} {v : Exp {}},
    Q1 v m1 ->
    resolve m1.heap v = some .btrue ∨ resolve m1.heap v = some .bfalse) ->
  (h_true : ∀ {m1 : Memory} {v : Exp {}},
    (m1.subsumes m) ->
    Q1 v m1 ->
    resolve m1.heap v = some .btrue ->
    Eval C m1 e2 Q) ->
  (h_false : ∀ {m1 : Memory} {v : Exp {}},
    (m1.subsumes m) ->
    Q1 v m1 ->
    resolve m1.heap v = some .bfalse ->
    Eval C m1 e3 Q) ->
  Eval C m (.cond x e2 e3) Q
| eval_par :
  Eval C1 m e1 Q ->
  Eval C2 m e2 Q ->
  Eval (C1 ∪ C2) m (.par e1 e2) Q

theorem eval_monotonic {m1 m2 : Memory}
  (hpred : Q.is_monotonic)
  (hbool : Q.is_bool_independent)
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
      -- Destructure subsumption to get the value in m2
      obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
      -- For value cells, subsumption requires equality
      simp [Cell.subsumes] at hsub_v
      subst hsub_v
      apply Eval.eval_apply
      · exact hx2
      · apply ih hpred hbool hsub (by
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
            exact hwf_y)
  case eval_invoke hmem hx hy hQ =>
    -- Destructure subsumptions
    obtain ⟨v'x, hx2, hsub_vx⟩ := hsub _ _ hx
    obtain ⟨v'y, hy2, hsub_vy⟩ := hsub _ _ hy
    -- For basic capability cells, subsumption requires equality
    simp [Cell.subsumes] at hsub_vx
    subst hsub_vx
    -- For value cells, subsumption requires equality
    simp [Cell.subsumes] at hsub_vy
    subst hsub_vy
    apply Eval.eval_invoke
    · exact hmem
    · exact hx2
    · exact hy2
    · apply hpred
      · apply Exp.WfInHeap.wf_unit
      · exact hsub
      · exact hQ
  case eval_tapply hx _ ih =>
    -- Destructure subsumption to get the value in m2
    obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
    -- For value cells, subsumption requires equality
    simp [Cell.subsumes] at hsub_v
    subst hsub_v
    apply Eval.eval_tapply
    · exact hx2
    · apply ih hpred hbool hsub (by
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
          apply Ty.WfInHeap.wf_top)
  case eval_capply hx _ ih =>
    -- Extract well-formedness of the capability application
    cases hwf with
    | wf_capp hwf_x hwf_cs =>
      -- Destructure subsumption to get the value in m2
      obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
      -- For value cells, subsumption requires equality
      simp [Cell.subsumes] at hsub_v
      subst hsub_v
      apply Eval.eval_capply
      · exact hx2
      · apply ih hpred hbool hsub (by
          -- Need: Exp.WfInHeap (e.subst (Subst.openCVar CS)) m1.heap
          -- Use Exp.wf_subst with Subst.wf_openCVar
          apply Exp.wf_subst
          · -- Need: Exp.WfInHeap e m1.heap
            -- Get it from Memory.wf_lookup and inversion
            have hwf_cabs := Memory.wf_lookup hx
            have ⟨_, hwf_e⟩ := Exp.wf_inv_cabs hwf_cabs
            exact hwf_e
          · -- Show: (Subst.openCVar CS).WfInHeap m1.heap
            apply Subst.wf_openCVar
            exact hwf_cs)
  case eval_letin Q1 hpred0 hbool0 eval_e1 h_nonstuck_orig h_val_orig h_var_orig ih ih_val ih_var =>
    rename_i C_orig e1_orig Q_orig e2_orig m_orig
    -- Use inversion to extract well-formedness of subexpressions
    have ⟨hwf1, hwf2⟩ := Exp.wf_inv_letin hwf
    -- Apply IH for e1 with well-formedness
    have eval_e1' := ih hpred0 hbool0 hsub hwf1
    apply Eval.eval_letin (Q1:=Q1) hpred0 hbool0 eval_e1'
    -- Provide the h_nonstuck condition
    case h_nonstuck =>
      intro m1 v hQ_orig
      exact h_nonstuck_orig hQ_orig
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
      apply ih_var hs_orig hwf_x hq1 hpred hbool
      · exact Memory.subsumes_refl _
      · -- Need: (e2_orig.subst (Subst.openVar x)).WfInHeap m_ext'.heap
        -- First, lift hwf2 to m_ext'.heap using monotonicity
        have hwf2_ext : Exp.WfInHeap e2_orig m_ext'.heap := Exp.wf_monotonic hs_orig hwf2
        -- Then apply substitution preservation
        apply Exp.wf_subst hwf2_ext
        apply Subst.wf_openVar hwf_x
  case eval_unpack Q1 hpred0 hbool0 eval_e1 h_nonstuck_orig h_val_orig ih ih_val =>
    rename_i C_orig e1_orig Q_orig e2_orig m_orig
    -- Use inversion to extract well-formedness of subexpressions
    have ⟨hwf1, hwf2⟩ := Exp.wf_inv_unpack hwf
    -- Apply IH for e1 with well-formedness
    have eval_e1' := ih hpred0 hbool0 hsub hwf1
    apply Eval.eval_unpack (Q1:=Q1) hpred0 hbool0 eval_e1'
    -- Provide the h_nonstuck condition
    case h_nonstuck =>
      intro m1 v hQ_orig
      exact h_nonstuck_orig hQ_orig
    case h_val =>
      intro m_ext' x cs hs_ext' hwf_x hwf_cs hq1
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      apply ih_val hs_orig hwf_x hwf_cs hq1 hpred hbool
      · exact Memory.subsumes_refl _
      · -- Need: (e2.subst (Subst.unpack cs x)).WfInHeap m_ext'.heap
        -- Lift hwf2 to m_ext'.heap using monotonicity
        have hwf2_ext : Exp.WfInHeap e2_orig m_ext'.heap := Exp.wf_monotonic hs_orig hwf2
        -- Apply substitution preservation
        apply Exp.wf_subst hwf2_ext
        -- Need: (Subst.unpack cs x).WfInHeap m_ext'.heap
        apply Subst.wf_unpack hwf_cs hwf_x
  case eval_read hcov hmem hx hQ =>
    -- New rule: first lookup reader at x, then lookup mcell at y (where reader points)
    -- hcov : C.covers .ro y
    -- hmem : m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩)
    -- hx : m.lookup y = some (.capability (.mcell b))
    -- hQ : Q (if b then .btrue else .bfalse) m
    rename_i y hv R m_orig b
    -- From subsumption, m2 must have the same reader val at x
    obtain ⟨cx, hx2, hsub_x⟩ := hsub _ _ hmem
    -- For value cells, subsumption requires equality
    simp [Cell.subsumes] at hsub_x
    subst hsub_x
    -- From subsumption, m2 must also have an mcell at y (possibly different boolean)
    obtain ⟨cy, hy2, hsub_y⟩ := hsub _ _ hx
    -- cy must be an mcell (possibly with different boolean)
    cases cy
    case val v =>
      -- Contradiction: val cannot subsume capability
      simp [Cell.subsumes] at hsub_y
    case masked =>
      -- Contradiction: masked cannot subsume mcell
      simp [Cell.subsumes] at hsub_y
    case capability info =>
      cases info
      case basic =>
        -- Contradiction: basic cannot subsume mcell
        simp [Cell.subsumes] at hsub_y
      case mcell b' =>
        -- Good! m2 has an mcell at y with boolean b'
        -- Need to show: Q (if b' then .btrue else .bfalse) m2
        -- We have: Q (if b then .btrue else .bfalse) m_orig
        -- Use bool independence: Q treats btrue and bfalse the same
        apply Eval.eval_read hcov hx2 hy2
        -- Goal: Q (if b' then .btrue else .bfalse) m2
        by_cases hb : b
        · -- b = true, so we have Q .btrue m_orig
          subst hb
          simp at hQ
          by_cases hb' : b' = true
          · -- b' = true, need Q .btrue m2
            subst hb'
            simp
            exact hpred (by constructor) hsub hQ
          · -- b' = false, need Q .bfalse m2
            -- Convert ¬b' = true to b' = false
            simp at hb'
            subst hb'
            simp
            rw [←hbool]
            exact hpred (by constructor) hsub hQ
        · -- b = false, so we have Q .bfalse m_orig
          simp at hb
          subst hb
          simp at hQ
          by_cases hb' : b' = true
          · -- b' = true, need Q .btrue m2
            subst hb'
            simp
            rw [hbool]
            exact hpred (by constructor) hsub hQ
          · -- b' = false, need Q .bfalse m2
            -- Convert ¬b' = true to b' = false
            simp at hb'
            subst hb'
            simp
            exact hpred (by constructor) hsub hQ
  case eval_write_true hmem hx hy hQ =>
    -- From subsumption, m2 must also have an mcell at x (possibly different value)
    -- and the same val at y
    obtain ⟨cx, hx2, hsub_x⟩ := hsub _ _ hx
    obtain ⟨cy, hy2, hsub_y⟩ := hsub _ _ hy
    -- cx must be an mcell (possibly with different boolean)
    cases cx
    case val v =>
      -- Contradiction: val cannot subsume capability
      simp [Cell.subsumes] at hsub_x
    case capability info =>
      cases info
      case basic =>
        -- Contradiction: basic cannot subsume mcell
        simp [Cell.subsumes] at hsub_x
      case mcell b' =>
        -- Good! m2 has an mcell at x
        -- cy must be the same val as in m1 (subsumption is equality for vals)
        simp [Cell.subsumes] at hsub_y
        subst hsub_y
        -- Now we can apply eval_write_true with m2
        apply Eval.eval_write_true hmem (hx := hx2) hy2
        -- Need to show: Q .unit (m2.update_mcell x true ⟨b', hx2⟩)
        -- We have: Q .unit (m1.update_mcell x true ⟨_, hx⟩)
        -- Use monotonicity with update_mcell_subsumes_compat
        apply hpred
        · -- unit is well-formed in any heap
          constructor
        · apply Memory.update_mcell_subsumes_compat _ _
              (Exists.intro _ hx) (Exists.intro _ hx2) hsub
        · exact hQ
    case masked =>
      -- Contradiction: masked cannot subsume mcell
      simp [Cell.subsumes] at hsub_x
  case eval_write_false hmem hx hy hQ =>
    -- Symmetric to eval_write_true
    obtain ⟨cx, hx2, hsub_x⟩ := hsub _ _ hx
    obtain ⟨cy, hy2, hsub_y⟩ := hsub _ _ hy
    cases cx
    case val v =>
      simp [Cell.subsumes] at hsub_x
    case capability info =>
      cases info
      case basic =>
        simp [Cell.subsumes] at hsub_x
      case mcell b' =>
        simp [Cell.subsumes] at hsub_y
        subst hsub_y
        apply Eval.eval_write_false hmem (hx := hx2) hy2
        apply hpred
        · constructor
        · apply Memory.update_mcell_subsumes_compat _ _
              (Exists.intro _ hx) (Exists.intro _ hx2) hsub
        · exact hQ
    case masked =>
      simp [Cell.subsumes] at hsub_x
  case eval_cond Q1 hpred_guard hbool_guard eval_e1 h_nonstuck h_true h_false
      ih_guard ih_true ih_false =>
    -- Extract well-formedness of the guard and both branches
    have ⟨hwf_x, hwf2, hwf3⟩ := Exp.wf_inv_cond hwf
    -- Build well-formedness of (.var x) in original heap
    have hwf_var : Exp.WfInHeap (.var _) _ := Exp.WfInHeap.wf_var hwf_x
    have eval_e1' := ih_guard hpred_guard hbool_guard hsub hwf_var
    apply Eval.eval_cond (Q1:=Q1) hpred_guard hbool_guard eval_e1'
    · intro m_guard v hQ1
      exact h_nonstuck hQ1
    · intro m_branch v hs hQ1 hres
      have hs_orig := Memory.subsumes_trans hs hsub
      exact h_true hs_orig hQ1 hres
    · intro m_branch v hs hQ1 hres
      have hs_orig := Memory.subsumes_trans hs hsub
      exact h_false hs_orig hQ1 hres
  case eval_par ih1 ih2 =>
    -- Extract well-formedness of both branches
    cases hwf with
    | wf_par hwf1 hwf2 =>
      apply Eval.eval_par
      · exact ih1 hpred hbool hsub hwf1
      · exact ih2 hpred hbool hsub hwf2

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
  case eval_letin _ Q0 hpred hbool0 he1 h_nonstuck h_val h_var ih ih_val ih_var =>
    specialize ih (by apply Mpost.entails_after_refl)
    apply Eval.eval_letin (Q1:=Q0) hpred hbool0 ih
    case h_nonstuck =>
      intro m1 v hQ0
      exact h_nonstuck hQ0
    case h_val =>
      intro m1 v hs1 hv hwf_v hq1 l' hfresh
      apply ih_val hs1 hv hwf_v hq1 l' hfresh
      apply Mpost.entails_after_subsumes himp
      apply Memory.subsumes_trans
        (Memory.extend_val_subsumes _ _ _ hwf_v rfl hfresh) hs1
    case h_var =>
      intro m1 x hs1 hwf_x hq1
      apply ih_var hs1 hwf_x hq1
      apply Mpost.entails_after_subsumes himp
      apply hs1
  case eval_unpack _ Q0 hpred hbool0 he1 h_nonstuck _ ih ih_val =>
    specialize ih (by apply Mpost.entails_after_refl)
    apply Eval.eval_unpack (Q1:=Q0) hpred hbool0 ih
    case h_nonstuck =>
      intro m1 v hQ0
      exact h_nonstuck hQ0
    case h_val =>
      intro m1 x cs hs1 hwf_x hwf_cs hq1
      apply ih_val hs1 hwf_x hwf_cs hq1
      apply Mpost.entails_after_subsumes himp
      apply hs1
  case eval_read hcov hmem hx hQ =>
    apply Eval.eval_read hcov hmem hx
    apply himp _ _ _ hQ
    apply Memory.subsumes_refl
  case eval_write_true hmem hx hy hQ =>
    apply Eval.eval_write_true hmem hx hy
    apply himp _ _ _ hQ
    apply Memory.update_mcell_subsumes
  case eval_write_false hmem hx hy hQ =>
    apply Eval.eval_write_false hmem hx hy
    apply himp _ _ _ hQ
    apply Memory.update_mcell_subsumes
  case eval_cond Q1 hpred_guard hbool_guard eval_e1 h_nonstuck h_true h_false
      ih_guard ih_true ih_false =>
    -- Strengthen the induction hypothesis for the guard evaluation
    have eval_e1' := ih_guard (Q2:=Q1) (by intro _ _ _ h; exact h)
    apply Eval.eval_cond (Q1:=Q1) hpred_guard hbool_guard eval_e1'
    case h_nonstuck =>
      intro m1 v hQ0
      exact h_nonstuck hQ0
    case h_true =>
      intro m1 v hsub hq1 hres
      apply ih_true hsub hq1 hres
      apply Mpost.entails_after_subsumes himp
      exact hsub
    case h_false =>
      intro m1 v hsub hq1 hres
      apply ih_false hsub hq1 hres
      apply Mpost.entails_after_subsumes himp
      exact hsub
  case eval_par ih1 ih2 =>
    apply Eval.eval_par
    · exact ih1 himp
    · exact ih2 himp

theorem eval_post_monotonic {Q1 Q2 : Mpost}
  (himp : Q1.entails Q2)
  (heval : Eval C m e Q1) :
  Eval C m e Q2 := by
  apply eval_post_monotonic_general _ heval
  apply Mpost.entails_to_entails_after himp

theorem eval_capability_set_monotonic {A1 A2 : CapabilitySet}
  (heval : Eval A1 m e Q)
  (hsub : A1 ⊆ A2) :
  Eval A2 m e Q := by
  induction heval
  case eval_val hv hQ =>
    exact Eval.eval_val hv hQ
  case eval_var hQ =>
    exact Eval.eval_var hQ
  case eval_apply hlookup _ ih =>
    exact Eval.eval_apply hlookup (ih hsub)
  case eval_invoke hcov hlookup_x hlookup_y hQ =>
    exact Eval.eval_invoke (CapabilitySet.subset_preserves_covers hsub hcov) hlookup_x hlookup_y hQ
  case eval_tapply hlookup _ ih =>
    exact Eval.eval_tapply hlookup (ih hsub)
  case eval_capply hlookup _ ih =>
    exact Eval.eval_capply hlookup (ih hsub)
  case eval_letin =>
    rename_i hpred_mono hbool_mono heval_e1 h_nonstuck h_val h_var ih_e1 ih_val ih_var
    apply Eval.eval_letin hpred_mono hbool_mono (ih_e1 hsub)
    · intro m1 v hQ
      exact h_nonstuck hQ
    · intro m1 v hs1 hv hwf_v hq1 l' hfresh
      exact ih_val hs1 hv hwf_v hq1 l' hfresh hsub
    · intro m1 x hs1 hwf_x hq1
      exact ih_var hs1 hwf_x hq1 hsub
  case eval_unpack =>
    rename_i hpred_mono hbool_mono heval_e1 h_nonstuck h_val ih_e1 ih_val
    apply Eval.eval_unpack hpred_mono hbool_mono (ih_e1 hsub)
    · intro m1 v hQ
      exact h_nonstuck hQ
    · intro m1 x cs hs1 hwf_x hwf_cs hq1
      exact ih_val hs1 hwf_x hwf_cs hq1 hsub
  case eval_read hcov hlookup_reader hlookup_mcell hQ =>
    exact Eval.eval_read
      (CapabilitySet.subset_preserves_covers hsub hcov) hlookup_reader hlookup_mcell hQ
  case eval_write_true hcov hlookup_x hlookup_y hQ =>
    exact Eval.eval_write_true
      (CapabilitySet.subset_preserves_covers hsub hcov) hlookup_x hlookup_y hQ
  case eval_write_false hcov hlookup_x hlookup_y hQ =>
    exact Eval.eval_write_false
      (CapabilitySet.subset_preserves_covers hsub hcov) hlookup_x hlookup_y hQ
  case eval_cond Q1 hpred_guard hbool_guard heval_e1 h_nonstuck h_true h_false
      ih_e1 ih_true ih_false =>
    apply Eval.eval_cond (Q1:=Q1) hpred_guard hbool_guard (ih_e1 hsub)
    · intro m1 v hQ
      exact h_nonstuck hQ
    · intro m1 v hs1 hq1 hres
      exact ih_true hs1 hq1 hres hsub
    · intro m1 v hs1 hq1 hres
      exact ih_false hs1 hq1 hres hsub
  case eval_par ih1 ih2 =>
    exact Eval.eval_par (ih1 hsub) (ih2 hsub)

end Capybara
