import Semantic.CoreCapybara.Syntax
import Semantic.CoreCapybara.Substitution
import Semantic.CoreCapybara.Semantics.Heap

namespace CoreCapybara

inductive Eval : CapabilitySet -> Memory -> Exp {} -> Mpost -> Prop where
| eval_pack :
  (cs.reachability m).to_drop ⊆ C ->  -- Consumed capabilities are counted as used
  (hQ : Q (.pack cs x) m) ->
  Eval C m (.pack cs x) Q
| eval_alloc {m : Memory} {x : Nat} {b : Bool} {hv R} :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  (h_post : ∀ l (hfresh : m.heap l = none),
    Q (.pack (.var (.M .epsilon) (.free l)) (.free l)) (m.extend_mcell l b hfresh)) ->
  Eval C m (.alloc (.free x)) Q
| eval_val :
  (hv : Exp.IsSimpleVal v) ->
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
  C.covers (.access .epsilon) x ->
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
| eval_wrap :
  Q (.boxed cs Ψ e) m ->
  Eval C m (.boxed cs Ψ e) Q
| eval_unwrap {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩) ->
  Eval C m e Q ->
  Eval C m (.unwrap (.free x)) Q
| eval_letin {m : Memory} {Q1 : Mpost} :
  (hpred : Q1.is_monotonic) ->
  (hbool : Q1.is_bool_independent) ->
  Eval C1 m e1 Q1 ->
  (h_nonstuck : ∀ {m1 : Memory} {v : Exp {}},
    Q1 v m1 ->
    v.IsSimpleAns ∧
    Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {m1} {v : Exp {}},
    (m1.subsumes m) ->
    (m1.is_compatible C2) ->
    (hv : Exp.IsSimpleVal v) ->
    (hwf_v : Exp.WfInHeap v m1.heap) ->
    Q1 v m1 ->
    ∀ l'
      (hfresh : m1.lookup l' = none),
      Eval C2
        (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩
          hwf_v rfl hfresh)
        (e2.subst (Subst.openVar (.free l')))
        Q) ->
  (h_var : ∀ {m1} {x : Var .var {}},
    (m1.subsumes m) ->
    (m1.is_compatible C2) ->
    (hwf_x : x.WfInHeap m1.heap) ->
    Q1 (.var x) m1 ->
    Eval C2 m1 (e2.subst (Subst.openVar x)) Q) ->
  (hseq : CapabilitySet.SeqComp C1 C2) ->
  (hagg : C1 ∪ C2 ⊆ Cagg) ->
  Eval Cagg m (.letin e1 e2) Q
| eval_unpack {m : Memory} {Q1 : Mpost} :
  (hpred : Q1.is_monotonic) ->
  (hbool : Q1.is_bool_independent) ->
  Eval C1 m e1 Q1 ->
  (h_nonstuck : ∀ {m1 : Memory} {v : Exp {}},
    Q1 v m1 ->
    v.IsPack ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {m1} {x : Var .var {}} {cs : CaptureSet {}},
    (m1.subsumes m) ->
    (m1.is_compatible
      (C2 ∪ (cs.reachability m1) ∪ (cs.reachability m1).to_drop)) ->
    (hwf_x : x.WfInHeap m1.heap) ->
    (hwf_cs : cs.WfInHeap m1.heap) ->
    Q1 (.pack cs x) m1 ->
    let R := cs.reachability m1
    Eval (C2 ∪ R ∪ R.to_drop) m1 (e2.subst (Subst.unpack cs x)) Q) ->
  (hseq : CapabilitySet.SeqComp C1 C2) ->
  (hagg : C1 ∪ C2 ⊆ Cagg) ->
  Eval Cagg m (.unpack e1 e2) Q
| eval_read {m : Memory} {x : Nat} {b : Bool} :
  C.covers (.access .ro) y ->
  m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  Q (if b then .btrue else .bfalse) m ->
  Eval C m (.read (.free x)) Q
| eval_write_true {m : Memory} {x y : Nat} :
  C.covers (.access .epsilon) x ->
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Q .unit (m.update_mcell x true .live ⟨b0, hx⟩) ->
  Eval C m (.write (.free x) (.free y)) Q
| eval_write_false {m : Memory} {x y : Nat} :
  C.covers (.access .epsilon) x ->
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Q .unit (m.update_mcell x false .live ⟨b0, hx⟩) ->
  Eval C m (.write (.free x) (.free y)) Q
| eval_drop :
  (hx : m.lookup x = some (.capability (.mcell b .live))) ->
  Q .unit (m.drop_mcell x ⟨b, hx⟩) ->
  C.covers .drop x ->
  Eval C m (.drop (.free x)) Q
| eval_cond {m : Memory} {x : Var .var {}} :
  (hres : resolve m.heap (.var x) = some .btrue ∨ resolve m.heap (.var x) = some .bfalse) ->
  (h_true : resolve m.heap (.var x) = some .btrue → Eval C m e2 Q) ->
  (h_false : resolve m.heap (.var x) = some .bfalse → Eval C m e3 Q) ->
  Eval C m (.cond x e2 e3) Q
| eval_par :
  Eval C1 m e1 Q ->
  Eval C2 m e2 Q ->
  CapabilitySet.Noninterference C1 C2 ->
  (C1 ∪ C2) ⊆ C' ->
  Eval C' m (.par e1 e2) Q

/-- `Eval` on a variable does not change memory: the only rule that produces
    `Eval C m (.var x) Q` is `eval_var`, which preserves `m`. So `Q` must hold at
    `(.var x)` and the original `m` — no cells were dropped along the way. -/
theorem Eval.var_inv {C : CapabilitySet} {m : Memory} {x : Var .var {}} {Q : Mpost}
    (heval : Eval C m (.var x) Q) : Q (.var x) m := by
  cases heval with
  | eval_val hv _ => cases hv
  | eval_var hQ => exact hQ

theorem eval_monotonic {m1 m2 : Memory}
  (hpred : Q.is_monotonic)
  (hbool : Q.is_bool_independent)
  (hsub : m2.subsumes m1)
  (hcompat : m2.is_compatible C)
  (hwf : Exp.WfInHeap e m1.heap)
  (heval : Eval C m1 e Q) :
  Eval C m2 e Q := by
  induction heval generalizing m2
  case eval_pack hsub_cs hQ =>
    cases hwf with
    | wf_pack hwf_cs hwf_x =>
      apply Eval.eval_pack
      · rw [CaptureSet.reachability_monotonic hsub _ hwf_cs]
        exact hsub_cs
      · apply hpred (Exp.WfInHeap.wf_pack hwf_cs hwf_x) hsub hQ
  case eval_alloc hlookup h_post =>
    rename_i m_orig _ b _ _
    -- Lift the lookup of x to m2.
    obtain ⟨v', hlookup', hsub_v⟩ := hsub _ _ hlookup
    simp only [Cell.subsumes] at hsub_v
    subst hsub_v
    apply Eval.eval_alloc hlookup'
    intro l hfresh2
    -- m2.heap l = none implies m_orig.heap l = none.
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
    · -- (.pack (.var .epsilon (.free l)) (.free l)).WfInHeap
      exact Exp.WfInHeap.wf_pack
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
    -- Extract well-formedness of the application
    cases hwf with
    | wf_app hwf_x hwf_y =>
      -- Destructure subsumption to get the value in m2
      obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
      -- For value cells, subsumption requires equality
      simp only [Cell.subsumes] at hsub_v
      subst hsub_v
      apply Eval.eval_apply
      · exact hx2
      · apply ih hpred hbool hsub hcompat (by
          apply Exp.wf_subst
          · have hwf_abs := Memory.wf_lookup hx
            have ⟨_, _, hwf_e⟩ := Exp.wf_inv_abs hwf_abs
            exact hwf_e
          · apply Subst.wf_openVar
            exact hwf_y)
  case eval_invoke hmem hx hy hQ =>
    -- Destructure subsumptions
    obtain ⟨v'x, hx2, hsub_vx⟩ := hsub _ _ hx
    obtain ⟨v'y, hy2, hsub_vy⟩ := hsub _ _ hy
    -- For basic capability cells, subsumption requires equality
    simp only [Cell.subsumes] at hsub_vx
    subst hsub_vx
    -- For value cells, subsumption requires equality
    simp only [Cell.subsumes] at hsub_vy
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
    simp only [Cell.subsumes] at hsub_v
    subst hsub_v
    apply Eval.eval_tapply
    · exact hx2
    · apply ih hpred hbool hsub hcompat (by
        apply Exp.wf_subst
        · have hwf_tabs := Memory.wf_lookup hx
          have ⟨_, _, hwf_e⟩ := Exp.wf_inv_tabs hwf_tabs
          exact hwf_e
        · apply Subst.wf_openTVar
          apply Ty.WfInHeap.wf_top)
  case eval_capply hx _ ih =>
    -- Extract well-formedness of the capability application
    cases hwf with
    | wf_capp hwf_x hwf_cs =>
      -- Destructure subsumption to get the value in m2
      obtain ⟨v', hx2, hsub_v⟩ := hsub _ _ hx
      -- For value cells, subsumption requires equality
      simp only [Cell.subsumes] at hsub_v
      subst hsub_v
      apply Eval.eval_capply
      · exact hx2
      · apply ih hpred hbool hsub hcompat (by
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
      apply ih hpred hbool hsub hcompat
      have hwf_boxed := Memory.wf_lookup hx
      cases hwf_boxed with
      | wf_boxed _ _ hwf_e =>
        exact hwf_e
  case eval_letin Q1 hpred0 hbool0 eval_e1 h_nonstuck_orig h_val_orig
      h_var_orig hseq0 hagg0 ih _ _ =>
    have ⟨hwf1, _hwf2⟩ := Exp.wf_inv_letin hwf
    have hcompat_union := Memory.is_compatible_subset hagg0 hcompat
    have hcompat_C1 := Memory.is_compatible_union_left hcompat_union
    have eval_e1' := ih hpred0 hbool0 hsub hcompat_C1 hwf1
    apply Eval.eval_letin (Q1:=Q1) hpred0 hbool0 eval_e1'
    case h_nonstuck =>
      intro m1 v hQ_orig
      exact h_nonstuck_orig hQ_orig
    case h_val =>
      intro m_ext' v hs_ext' hcompat_ext' hv hwf_v hq1 l' hfresh
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      exact h_val_orig hs_orig hcompat_ext' hv hwf_v hq1 l' hfresh
    case h_var =>
      intro m_ext' x hs_ext' hcompat_ext' hwf_x hq1
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      exact h_var_orig hs_orig hcompat_ext' hwf_x hq1
    case hseq => exact hseq0
    case hagg => exact hagg0
  case eval_unpack Q1 hpred0 hbool0 eval_e1 h_nonstuck_orig h_val_orig hseq0 hagg0 ih _ =>
    have ⟨hwf1, _hwf2⟩ := Exp.wf_inv_unpack hwf
    have hcompat_union := Memory.is_compatible_subset hagg0 hcompat
    have hcompat_C1 := Memory.is_compatible_union_left hcompat_union
    have eval_e1' := ih hpred0 hbool0 hsub hcompat_C1 hwf1
    apply Eval.eval_unpack (Q1:=Q1) hpred0 hbool0 eval_e1'
    case h_nonstuck =>
      intro m1 v hQ_orig
      exact h_nonstuck_orig hQ_orig
    case h_val =>
      intro m_ext' x cs hs_ext' hcompat_ext' hwf_x hwf_cs hq1
      have hs_orig := Memory.subsumes_trans hs_ext' hsub
      exact h_val_orig hs_orig hcompat_ext' hwf_x hwf_cs hq1
    case hseq => exact hseq0
    case hagg => exact hagg0
  case eval_read hcov hmem hx hQ =>
    -- hcov : C.covers (.access .ro) y
    -- hmem : m_orig.lookup x = some (.val ⟨.reader (.free y), hv, R⟩)
    -- hx : m_orig.lookup y = some (.capability (.mcell b .live))
    -- hQ : Q (if b then .btrue else .bfalse) m_orig
    rename_i y _hv _R _m_orig b
    obtain ⟨cx, hx2, hsub_x⟩ := hsub _ _ hmem
    simp only [Cell.subsumes] at hsub_x
    subst hsub_x
    obtain ⟨cy, hy2, hsub_y⟩ := hsub _ _ hx
    cases cy
    case val v => cases hsub_y
    case masked => cases hsub_y
    case capability info =>
      cases info
      case basic => cases hsub_y
      case mcell b' ℓ' =>
        -- `hcompat` + `hcov` force ℓ' = .live: y is in C (via covers), and
        -- the m2-cell at y is an mcell, so it must be live.
        obtain ⟨mu', hmem_y, _⟩ := CapabilitySet.covers_imp_exists_hasmem hcov
        have hℓ' : ℓ' = .live := hcompat mu' _ b' ℓ' hmem_y hy2
        subst hℓ'
        apply Eval.eval_read hcov hx2 hy2
        -- Bool reasoning (unchanged): transfer Q across m_orig → m2 and b → b'
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
  case eval_write_true hmem hx hy hQ =>
    -- hmem : C.covers (.access .epsilon) x
    obtain ⟨cx, hx2, hsub_x⟩ := hsub _ _ hx
    obtain ⟨cy, hy2, hsub_y⟩ := hsub _ _ hy
    cases cx
    case val v => simp [Cell.subsumes] at hsub_x
    case capability info =>
      cases info
      case basic => cases hsub_x
      case mcell b' ℓ' =>
        -- `hcompat` + `hmem` force ℓ' = .live.
        obtain ⟨mu', hmem_x, _⟩ := CapabilitySet.covers_imp_exists_hasmem hmem
        have hℓ' : ℓ' = .live := hcompat mu' _ b' ℓ' hmem_x hx2
        subst hℓ'
        simp only [Cell.subsumes] at hsub_y
        subst hsub_y
        apply Eval.eval_write_true hmem (hx := hx2) hy2
        apply hpred
        · constructor
        · apply Memory.update_mcell_subsumes_compat _ _ _
              (Exists.intro _ hx) (Exists.intro _ hx2) hsub
        · exact hQ
    case masked => cases hsub_x
  case eval_write_false hmem hx hy hQ =>
    -- Symmetric to eval_write_true.
    obtain ⟨cx, hx2, hsub_x⟩ := hsub _ _ hx
    obtain ⟨cy, hy2, hsub_y⟩ := hsub _ _ hy
    cases cx
    case val v => simp [Cell.subsumes] at hsub_x
    case capability info =>
      cases info
      case basic => cases hsub_x
      case mcell b' ℓ' =>
        obtain ⟨mu', hmem_x, _⟩ := CapabilitySet.covers_imp_exists_hasmem hmem
        have hℓ' : ℓ' = .live := hcompat mu' _ b' ℓ' hmem_x hx2
        subst hℓ'
        simp only [Cell.subsumes] at hsub_y
        subst hsub_y
        apply Eval.eval_write_false hmem (hx := hx2) hy2
        apply hpred
        · constructor
        · apply Memory.update_mcell_subsumes_compat _ _ _
              (Exists.intro _ hx) (Exists.intro _ hx2) hsub
        · exact hQ
    case masked => cases hsub_x
  case eval_drop hx hQ hcov =>
    -- hx : m_orig.lookup x = some (.capability (.mcell b .live))
    -- hQ : Q .unit (m_orig.drop_mcell x ⟨b, hx⟩)
    -- hcov : C.covers .drop x
    obtain ⟨cx, hx2, hsub_x⟩ := hsub _ _ hx
    cases cx
    case val v => cases hsub_x
    case capability info =>
      cases info
      case basic => cases hsub_x
      case mcell b' ℓ' =>
        -- `hcompat` + `hcov` force ℓ' = .live.
        obtain ⟨mu', hmem_x, _⟩ := CapabilitySet.covers_imp_exists_hasmem hcov
        have hℓ' : ℓ' = .live := hcompat mu' _ b' ℓ' hmem_x hx2
        subst hℓ'
        apply Eval.eval_drop hx2 ?_ hcov
        apply hpred
        · constructor
        · exact Memory.drop_mcell_subsumes_compat _ ⟨_, hx⟩ ⟨_, hx2⟩ hsub
        · exact hQ
    case masked => cases hsub_x
  case eval_cond x hres h_true h_false ih_true ih_false =>
    rename_i _ _ _ m_orig
    have ⟨hwf_x, hwf2, hwf3⟩ := Exp.wf_inv_cond hwf
    -- Lift `hres` from m_orig to m2 via resolve monotonicity (val cells preserved).
    have hres' :
        resolve m2.heap (.var x) = some .btrue ∨ resolve m2.heap (.var x) = some .bfalse := by
      cases hres with
      | inl h => exact .inl (resolve_monotonic hsub h)
      | inr h => exact .inr (resolve_monotonic hsub h)
    apply Eval.eval_cond hres'
    · -- true branch
      intro hres_m2_true
      have hres_orig : resolve m_orig.heap (.var x) = some .btrue := by
        cases hres with
        | inl h => exact h
        | inr h =>
          have := resolve_monotonic hsub h
          rw [this] at hres_m2_true; cases hres_m2_true
      exact ih_true hres_orig hpred hbool hsub hcompat hwf2
    · -- false branch
      intro hres_m2_false
      have hres_orig : resolve m_orig.heap (.var x) = some .bfalse := by
        cases hres with
        | inl h =>
          have := resolve_monotonic hsub h
          rw [this] at hres_m2_false; cases hres_m2_false
        | inr h => exact h
      exact ih_false hres_orig hpred hbool hsub hcompat hwf3
  case eval_par hni hsub_cap ih1 ih2 =>
    -- Split compatibility along `C1 ∪ C2 ⊆ C'` for the two branches.
    cases hwf with
    | wf_par hwf1 hwf2 =>
      have hcompat_union := Memory.is_compatible_subset hsub_cap hcompat
      have hcompat1 := Memory.is_compatible_union_left hcompat_union
      have hcompat2 := Memory.is_compatible_union_right hcompat_union
      exact Eval.eval_par
        (ih1 hpred hbool hsub hcompat1 hwf1)
        (ih2 hpred hbool hsub hcompat2 hwf2)
        hni hsub_cap

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

theorem eval_post_monotonic_general {Q1 Q2 : Mpost}
  (himp : Q1.entails_after m Q2)
  (heval : Eval C m e Q1) :
  Eval C m e Q2 := by
  induction heval generalizing Q2
  case eval_pack hsub_cs hQ =>
    apply Eval.eval_pack hsub_cs
    apply himp _ (Memory.subsumes_refl _) _ hQ
  case eval_alloc hlookup h_post =>
    apply Eval.eval_alloc hlookup
    intro l hfresh
    apply himp _ (Memory.extend_mcell_subsumes _ _ _ hfresh) _ (h_post l hfresh)
  case eval_val v Q M hv hQ =>
    exact Eval.eval_val hv (himp M (Memory.subsumes_refl _) _ hQ)
  case eval_var Q1 M x hQ =>
    exact Eval.eval_var (himp M (Memory.subsumes_refl _) _ hQ)
  case eval_apply hx _ ih =>
    exact Eval.eval_apply hx (ih himp)
  case eval_invoke hmem hx hy hQ =>
    exact Eval.eval_invoke hmem hx hy (himp _ (Memory.subsumes_refl _) _ hQ)
  case eval_tapply hx _ ih =>
    exact Eval.eval_tapply hx (ih himp)
  case eval_capply hx _ ih =>
    exact Eval.eval_capply hx (ih himp)
  case eval_wrap hQ =>
    exact Eval.eval_wrap (himp _ (Memory.subsumes_refl _) _ hQ)
  case eval_unwrap hx _ ih =>
    exact Eval.eval_unwrap hx (ih himp)
  case eval_letin _ Q0 hpred hbool0 he1 h_nonstuck h_val h_var hseq hagg ih ih_val ih_var =>
    specialize ih (by apply Mpost.entails_after_refl)
    apply Eval.eval_letin (Q1:=Q0) hpred hbool0 ih
    case h_nonstuck =>
      intro m1 v hQ0
      exact h_nonstuck hQ0
    case h_val =>
      intro m1 v hs1 hcompat1 hv hwf_v hq1 l' hfresh
      apply ih_val hs1 hcompat1 hv hwf_v hq1 l' hfresh
      apply Mpost.entails_after_subsumes himp
      apply Memory.subsumes_trans
        (Memory.extend_val_subsumes _ _ _ hwf_v rfl hfresh) hs1
    case h_var =>
      intro m1 x hs1 hcompat1 hwf_x hq1
      apply ih_var hs1 hcompat1 hwf_x hq1
      apply Mpost.entails_after_subsumes himp
      apply hs1
    case hseq => exact hseq
    case hagg => exact hagg
  case eval_unpack _ Q0 hpred hbool0 he1 h_nonstuck _ hseq hagg ih ih_val =>
    specialize ih (by apply Mpost.entails_after_refl)
    apply Eval.eval_unpack (Q1:=Q0) hpred hbool0 ih
    case h_nonstuck =>
      intro m1 v hQ0
      exact h_nonstuck hQ0
    case h_val =>
      intro m1 x cs hs1 hcompat1 hwf_x hwf_cs hq1
      apply ih_val hs1 hcompat1 hwf_x hwf_cs hq1
      apply Mpost.entails_after_subsumes himp
      apply hs1
    case hseq => exact hseq
    case hagg => exact hagg
  case eval_read hcov hmem hx hQ =>
    exact Eval.eval_read hcov hmem hx (himp _ (Memory.subsumes_refl _) _ hQ)
  case eval_write_true hmem hx hy hQ =>
    apply Eval.eval_write_true hmem hx hy
    apply himp _ _ _ hQ
    apply Memory.update_mcell_subsumes
  case eval_write_false hmem hx hy hQ =>
    apply Eval.eval_write_false hmem hx hy
    apply himp _ _ _ hQ
    apply Memory.update_mcell_subsumes
  case eval_drop hx hQ hcov =>
    apply Eval.eval_drop hx ?_ hcov
    -- The dropped memory now subsumes the original (live → dead is allowed
    -- by the relaxed `Cell.subsumes`), so `himp` fires at the dropped memory.
    apply himp _ _ _ hQ
    apply Memory.drop_mcell_subsumes
  case eval_cond hres h_true h_false ih_true ih_false =>
    apply Eval.eval_cond hres
    · intro hres_true
      exact ih_true hres_true himp
    · intro hres_false
      exact ih_false hres_false himp
  case eval_par hni hsub_cap ih1 ih2 =>
    exact Eval.eval_par (ih1 himp) (ih2 himp) hni hsub_cap

theorem eval_post_monotonic {Q1 Q2 : Mpost}
  (himp : Q1.entails Q2)
  (heval : Eval C m e Q1) :
  Eval C m e Q2 :=
  eval_post_monotonic_general (Mpost.entails_to_entails_after himp) heval

theorem eval_capability_set_monotonic {A1 A2 : CapabilitySet}
  (heval : Eval A1 m e Q)
  (hsub : A1 ⊆ A2) :
  Eval A2 m e Q := by
  induction heval generalizing A2
  case eval_pack hsub_cs hQ =>
    exact Eval.eval_pack (CapabilitySet.Subset.trans hsub_cs hsub) hQ
  case eval_alloc hlookup h_post =>
    exact Eval.eval_alloc hlookup h_post
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
  case eval_wrap hQ =>
    exact Eval.eval_wrap hQ
  case eval_unwrap hlookup _ ih =>
    exact Eval.eval_unwrap hlookup (ih hsub)
  case eval_letin =>
    rename_i hpred_mono hbool_mono heval_e1 h_nonstuck h_val h_var hseq hagg
      ih_e1 ih_val ih_var
    -- `eval_letin` carries an explicit aggregation `hagg : C1 ∪ C2 ⊆ Cagg`.
    -- Since the original index `Cagg` satisfies `Cagg ⊆ A2`, we simply re-aggregate
    -- to `A2` via `C1 ∪ C2 ⊆ Cagg ⊆ A2`, keeping all sub-derivations unchanged.
    -- `hseq : SeqComp C1 C2` is preserved verbatim (C1, C2 unchanged).
    exact Eval.eval_letin hpred_mono hbool_mono heval_e1 h_nonstuck h_val h_var hseq
      (CapabilitySet.Subset.trans hagg hsub)
  case eval_unpack =>
    rename_i hpred_mono hbool_mono heval_e1 h_nonstuck h_val hseq hagg ih_e1 ih_val
    -- As with `eval_letin`: the explicit aggregation `hagg : C1 ∪ C2 ⊆ Cagg`
    -- re-aggregates to `A2` via `C1 ∪ C2 ⊆ Cagg ⊆ A2`; sub-derivations unchanged.
    exact Eval.eval_unpack hpred_mono hbool_mono heval_e1 h_nonstuck h_val hseq
      (CapabilitySet.Subset.trans hagg hsub)
  case eval_read hcov hlookup_reader hlookup_mcell hQ =>
    exact Eval.eval_read
      (CapabilitySet.subset_preserves_covers hsub hcov) hlookup_reader hlookup_mcell hQ
  case eval_write_true hcov hlookup_x hlookup_y hQ =>
    exact Eval.eval_write_true
      (CapabilitySet.subset_preserves_covers hsub hcov) hlookup_x hlookup_y hQ
  case eval_write_false hcov hlookup_x hlookup_y hQ =>
    exact Eval.eval_write_false
      (CapabilitySet.subset_preserves_covers hsub hcov) hlookup_x hlookup_y hQ
  case eval_drop hx hQ hcov =>
    exact Eval.eval_drop hx hQ (CapabilitySet.subset_preserves_covers hsub hcov)
  case eval_cond hres h_true h_false ih_true ih_false =>
    apply Eval.eval_cond hres
    · intro hres_true
      exact ih_true hres_true hsub
    · intro hres_false
      exact ih_false hres_false hsub
  case eval_par heval1 heval2 hni hsub_cap _ _ =>
    exact Eval.eval_par heval1 heval2 hni (CapabilitySet.Subset.trans hsub_cap hsub)

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
