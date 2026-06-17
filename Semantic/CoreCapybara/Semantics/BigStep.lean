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

/-- `extDropsFrom A l t`: `l` is dealloc'd in `t` before being allocated within
  `t`.  Only `.dealloc` events count — the *drop* footprint of `t` (drop-only
  sibling of `extTouches`), sharing `TraceOk`'s alloc exemption. -/
def Trace.extDropsFrom : List Nat -> Nat -> Trace -> Prop
| _, _, [] => False
| A, l, (.alloc l' :: t) => Trace.extDropsFrom (l' :: A) l t
| A, l, (.access _ _ :: t) => Trace.extDropsFrom A l t
| A, l, (.dealloc l' :: t) => (l = l' ∧ l ∉ A) ∨ Trace.extDropsFrom A l t

/-- `l` is *externally dropped* by `t`: dealloc'd before being allocated within
  `t`.  For a location live before `t` runs (never freshly allocated within `t`),
  this coincides with "dropped at all by `t`". -/
def Trace.extDrops (t : Trace) (l : Nat) : Prop := Trace.extDropsFrom [] l t

/-- Operational frame/liveness guarantee for an evaluation producing trace `t`
  and ending memory `m'` from `m`: every mutable cell **live in `m`** that is *not
  externally dropped* by `t` remains **live in `m'`** (the only event that kills an
  existing live cell is a `.dealloc`). -/
def Memory.FrameLive (m : Memory) (t : Trace) (m' : Memory) : Prop :=
  ∀ l b,
    m.lookup l = some (.capability (.mcell b .live)) ->
    ¬ Trace.extDrops t l ->
    ∃ b', m'.lookup l = some (.capability (.mcell b' .live))

/-- `FrameLive` composes along a fixed trace. -/
theorem Memory.FrameLive.trans {m1 m2 m3 : Memory} {t : Trace}
    (h12 : Memory.FrameLive m1 t m2) (h23 : Memory.FrameLive m2 t m3) :
    Memory.FrameLive m1 t m3 := by
  intro l b hlive hnd
  obtain ⟨b', hb'⟩ := h12 l b hlive hnd
  exact h23 l b' hb' hnd

/-- The identity step is `FrameLive` for any trace (no cell changes liveness). -/
theorem Memory.FrameLive.refl {m : Memory} {t : Trace} : Memory.FrameLive m t m :=
  fun _ b hl _ => ⟨b, hl⟩

/- ============================================================================
   ROUTE B: the OLD CPS `Eval` inductive is COMMENTED OUT below for reference.
   It is superseded by the relational `BigStep` relation and the new `def Eval`
   (preservation form) that follow this block.

   OLD doc — Trace-instrumented big-step evaluation:
   `Eval m e Q` means evaluating `e` from `m` produces a trace `t`, ending at a
   value/memory at which `Q t` holds.  The defect this refactor fixes: the
   `eval_letin`/`eval_unpack` continuations quantified over ABSTRACT `Q1`-triples
   `(t1, m1)`, not real `e1`-answers, so `m1`'s budget liveness was unknowable.
   ----------------------------------------------------------------------------

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
   ============================================================================ -/

/-- Relational big-step evaluation.  `BigStep m e t v m'` holds when evaluating
  `e` from memory `m` terminates at value `v` and final memory `m'`, recording
  the trace `t` of heap events.

  Unlike the old CPS `Eval`, the intermediate result of a `letin`/`unpack` here
  is an *actual* answer (`m1` is a genuine `e1`-result), which is exactly what
  lets the continuation observe a live budget — closing the frame gap.

  Per-rule traces agree with the old `Eval`. -/
inductive BigStep : Memory -> Exp {} -> Trace -> Exp {} -> Memory -> Prop where
| bs_pack {m : Memory} :
  BigStep m (.pack cs x) [] (.pack cs x) m
| bs_alloc {m : Memory} {x : Nat} {b : Bool} {hv R} {l : Nat} :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  (hfresh : m.heap l = none) ->
  BigStep m (.alloc (.free x)) [.alloc l]
    (.pack (.var (.M .epsilon) (.free l)) (.free l)) (m.extend_mcell l b hfresh)
| bs_val {m : Memory} {v : Exp {}} :
  (hv : Exp.IsSimpleVal v) ->
  BigStep m v [] v m
| bs_var {m : Memory} {x : Var .var {}} :
  BigStep m (.var x) [] (.var x) m
| bs_apply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  BigStep m (e.subst (Subst.openVar y)) t v m' ->
  BigStep m (.app (.free x) y) t v m'
| bs_invoke {m : Memory} {x : Nat} :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  BigStep m (.app (.free x) (.free y)) [.access .epsilon x] .unit m
| bs_tapply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R⟩) ->
  BigStep m (e.subst (Subst.openTVar .top)) t v m' ->
  BigStep m (.tapp (.free x) S) t v m'
| bs_capply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R⟩) ->
  BigStep m (e.subst (Subst.openCVar CS)) t v m' ->
  BigStep m (.capp (.free x) CS) t v m'
| bs_wrap {m : Memory} :
  BigStep m (.boxed cs Ψ e) [] (.boxed cs Ψ e) m
| bs_unwrap {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩) ->
  BigStep m e t v m' ->
  BigStep m (.unwrap (.free x)) t v m'
| bs_letin_val {m m1 m2 : Memory} {v : Exp {}} {l' : Nat} :
  BigStep m e1 t1 v m1 ->
  (hv : Exp.IsSimpleVal v) ->
  (hwf_v : Exp.WfInHeap v m1.heap) ->
  (hfresh : m1.lookup l' = none) ->
  BigStep (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
    (e2.subst (Subst.openVar (.free l'))) t2 v2 m2 ->
  BigStep m (.letin e1 e2) (t1 ++ t2) v2 m2
| bs_letin_var {m m1 m2 : Memory} {x : Var .var {}} :
  BigStep m e1 t1 (.var x) m1 ->
  BigStep m1 (e2.subst (Subst.openVar x)) t2 v2 m2 ->
  BigStep m (.letin e1 e2) (t1 ++ t2) v2 m2
| bs_unpack {m m1 m2 : Memory} {x : Var .var {}} {cs : CaptureSet {}} :
  BigStep m e1 t1 (.pack cs x) m1 ->
  BigStep m1 (e2.subst (Subst.unpack cs x)) t2 v2 m2 ->
  BigStep m (.unpack e1 e2) (t1 ++ t2) v2 m2
| bs_read {m : Memory} {x : Nat} {b : Bool} :
  m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  -- Faithful read: the result is the STORED bit `b`.
  BigStep m (.read (.free x)) [.access .ro y] (if b then .btrue else .bfalse) m
| bs_write_true {m : Memory} {x y : Nat} {b0 : Bool} {hv R} :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  BigStep m (.write (.free x) (.free y)) [.access .epsilon x] .unit
    (m.update_mcell x true .live ⟨b0, hx⟩)
| bs_write_false {m : Memory} {x y : Nat} {b0 : Bool} {hv R} :
  (hx : m.lookup x = some (.capability (.mcell b0 .live))) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  BigStep m (.write (.free x) (.free y)) [.access .epsilon x] .unit
    (m.update_mcell x false .live ⟨b0, hx⟩)
| bs_drop {m : Memory} {x : Nat} {b : Bool} :
  (hx : m.lookup x = some (.capability (.mcell b .live))) ->
  BigStep m (.drop (.free x)) [.dealloc x] .unit (m.drop_mcell x ⟨b, hx⟩)
| bs_cond_true {m : Memory} {x : Var .var {}} :
  resolve m.heap (.var x) = some .btrue ->
  BigStep m e2 t v m' ->
  BigStep m (.cond x e2 e3) t v m'
| bs_cond_false {m : Memory} {x : Var .var {}} :
  resolve m.heap (.var x) = some .bfalse ->
  BigStep m e3 t v m' ->
  BigStep m (.cond x e2 e3) t v m'
| bs_par_left {m : Memory} :
  BigStep m e1 t v m' ->
  BigStep m (.par e1 e2) t v m'
| bs_par_right {m : Memory} :
  BigStep m e2 t v m' ->
  BigStep m (.par e1 e2) t v m'

/-- Progress / safety predicate: `Safe m e` means evaluating `e` from `m` never
  gets stuck — every redex reached is reducible, and (inductively, since this is
  a least fixed point) every path reaches an answer.

  This is the old inductive `Eval`'s skeleton with the postcondition erased.  The
  one structural change from the old `Eval`: `letin`/`unpack` quantify their
  continuation over the *real* `BigStep` answers of the head (so the intermediate
  `m1` is a genuine result), instead of over abstract `Q1`-triples. -/
inductive Safe : Memory -> Exp {} -> Prop where
| ans {m : Memory} {e : Exp {}} :
  e.IsAns -> Safe m e
| alloc {m : Memory} {x : Nat} {b : Bool} {hv R} :
  m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) ->
  Safe m (.alloc (.free x))
| apply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  Safe m (e.subst (Subst.openVar y)) ->
  Safe m (.app (.free x) y)
| invoke {m : Memory} {x : Nat} :
  m.lookup x = some (.capability .basic) ->
  m.lookup y = some (.val ⟨.unit, hv, R⟩) ->
  Safe m (.app (.free x) (.free y))
| tapply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R⟩) ->
  Safe m (e.subst (Subst.openTVar .top)) ->
  Safe m (.tapp (.free x) S)
| capply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R⟩) ->
  Safe m (e.subst (Subst.openCVar CS)) ->
  Safe m (.capp (.free x) CS)
| unwrap {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩) ->
  Safe m e ->
  Safe m (.unwrap (.free x))
| letin {m : Memory} :
  Safe m e1 ->
  (h_ans : ∀ {m0 : Memory} {t1 v m1}, m0.subsumes m -> BigStep m0 e1 t1 v m1 ->
    v.IsSimpleAns ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {m0 : Memory} {t1 : Trace} {m1} {v : Exp {}},
    m0.subsumes m -> BigStep m0 e1 t1 v m1 -> (hv : Exp.IsSimpleVal v) ->
    (hwf_v : Exp.WfInHeap v m1.heap) ->
    ∀ l' (hfresh : m1.lookup l' = none),
      Safe (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
        (e2.subst (Subst.openVar (.free l')))) ->
  (h_var : ∀ {m0 : Memory} {t1 : Trace} {m1} {x : Var .var {}},
    m0.subsumes m -> BigStep m0 e1 t1 (.var x) m1 -> Safe m1 (e2.subst (Subst.openVar x))) ->
  Safe m (.letin e1 e2)
| unpack {m : Memory} :
  Safe m e1 ->
  (h_ans : ∀ {m0 : Memory} {t1 v m1}, m0.subsumes m -> BigStep m0 e1 t1 v m1 ->
    v.IsPack ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {m0 : Memory} {t1 : Trace} {m1} {x : Var .var {}} {cs : CaptureSet {}},
    m0.subsumes m -> BigStep m0 e1 t1 (.pack cs x) m1 -> Safe m1 (e2.subst (Subst.unpack cs x))) ->
  Safe m (.unpack e1 e2)
| read {m : Memory} {x : Nat} {b : Bool} :
  m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  Safe m (.read (.free x))
| write_true {m : Memory} {x y : Nat} {b0 : Bool} {hv R} :
  m.lookup x = some (.capability (.mcell b0 .live)) ->
  m.lookup y = some (.val ⟨.btrue, hv, R⟩) ->
  Safe m (.write (.free x) (.free y))
| write_false {m : Memory} {x y : Nat} {b0 : Bool} {hv R} :
  m.lookup x = some (.capability (.mcell b0 .live)) ->
  m.lookup y = some (.val ⟨.bfalse, hv, R⟩) ->
  Safe m (.write (.free x) (.free y))
| drop {m : Memory} {x : Nat} {b : Bool} :
  m.lookup x = some (.capability (.mcell b .live)) ->
  Safe m (.drop (.free x))
| cond {m : Memory} {x : Var .var {}} :
  (resolve m.heap (.var x) = some .btrue ∨ resolve m.heap (.var x) = some .bfalse) ->
  (resolve m.heap (.var x) = some .btrue -> Safe m e2) ->
  (resolve m.heap (.var x) = some .bfalse -> Safe m e3) ->
  Safe m (.cond x e2 e3)
| par {m : Memory} :
  Safe m e1 ->
  Safe m e2 ->
  Safe m (.par e1 e2)

/-- Trace-observing evaluation predicate (Route B): `e` from `m` is **safe**
  (never stuck — `Safe m e`) **and** every answer it reaches satisfies `Q`.

  Preservation is **robust over memory subsumption** (`∀ m0 ⊒ m`): every answer
  reached from *any* `m0 ⊒ m` satisfies `Q`.  This is what makes `Eval` Kripke-
  monotone under FAITHFUL reads — a read returns the stored bit, so a later
  `m2 ⊒ m1` may flip it and a `letin (read …) (cond …)` takes a different branch;
  quantifying over `m0 ⊒ m` covers that branch (the relational analogue of the
  old CPS `eval_letin`'s `Q1.is_bool_independent` field).  Safety is bundled in,
  so this is no weaker than the old inductive `Eval`. -/
def Eval (m : Memory) (e : Exp {}) (Q : Tpost) : Prop :=
  Safe m e ∧ (∀ {m0 : Memory} t v m', m0.subsumes m -> BigStep m0 e t v m' -> Q t v m')

/-- Every `BigStep` answer value is an answer (`IsAns`). -/
theorem BigStep.isAns {m e t v m'} (h : BigStep m e t v m') : v.IsAns := by
  induction h with
  | bs_pack => exact Exp.IsAns.is_val Exp.IsVal.pack
  | bs_alloc _ _ => exact Exp.IsAns.is_val Exp.IsVal.pack
  | bs_val hv => exact Exp.IsAns.is_val (by cases hv <;> constructor)
  | bs_var => exact Exp.IsAns.is_var
  | bs_apply _ _ ih => exact ih
  | bs_invoke _ _ => exact Exp.IsAns.is_val Exp.IsVal.unit
  | bs_tapply _ _ ih => exact ih
  | bs_capply _ _ ih => exact ih
  | bs_wrap => exact Exp.IsAns.is_val Exp.IsVal.boxed
  | bs_unwrap _ _ ih => exact ih
  | bs_letin_val _ _ _ _ _ _ ih => exact ih
  | bs_letin_var _ _ _ ih => exact ih
  | bs_unpack _ _ _ ih => exact ih
  | bs_read _ _ => exact Exp.IsAns.is_val (by split <;> constructor)
  | bs_write_true _ _ => exact Exp.IsAns.is_val Exp.IsVal.unit
  | bs_write_false _ _ => exact Exp.IsAns.is_val Exp.IsVal.unit
  | bs_drop _ => exact Exp.IsAns.is_val Exp.IsVal.unit
  | bs_cond_true _ _ ih => exact ih
  | bs_cond_false _ _ ih => exact ih
  | bs_par_left _ ih => exact ih
  | bs_par_right _ ih => exact ih

/-- `BigStep` evolves memory monotonically: the final memory subsumes the initial. -/
theorem BigStep.subsumes {m e t v m'} (h : BigStep m e t v m') : m'.subsumes m := by
  induction h with
  | bs_pack => exact Memory.subsumes_refl _
  | bs_alloc _ hfresh => exact Memory.extend_mcell_subsumes _ _ _ hfresh
  | bs_val _ => exact Memory.subsumes_refl _
  | bs_var => exact Memory.subsumes_refl _
  | bs_apply _ _ ih => exact ih
  | bs_invoke _ _ => exact Memory.subsumes_refl _
  | bs_tapply _ _ ih => exact ih
  | bs_capply _ _ ih => exact ih
  | bs_wrap => exact Memory.subsumes_refl _
  | bs_unwrap _ _ ih => exact ih
  | bs_letin_val _ _ hwf hfresh _ ih1 ih2 =>
    exact Memory.subsumes_trans ih2
      (Memory.subsumes_trans (Memory.extend_val_subsumes _ _ _ hwf rfl hfresh) ih1)
  | bs_letin_var _ _ ih1 ih2 => exact Memory.subsumes_trans ih2 ih1
  | bs_unpack _ _ ih1 ih2 => exact Memory.subsumes_trans ih2 ih1
  | bs_read _ _ => exact Memory.subsumes_refl _
  | bs_write_true hx _ => exact Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩
  | bs_write_false hx _ => exact Memory.update_mcell_subsumes _ _ _ _ ⟨_, hx⟩
  | bs_drop hx => exact Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩
  | bs_cond_true _ _ ih => exact ih
  | bs_cond_false _ _ ih => exact ih
  | bs_par_left _ ih => exact ih
  | bs_par_right _ ih => exact ih

/-- `Eval` on a variable does not change memory and emits no events: the only
    `BigStep` answer of `.var x` is `(.var x)` itself with an empty trace. -/
theorem Eval.var_inv {m : Memory} {x : Var .var {}} {Q : Tpost}
    (heval : Eval m (.var x) Q) : Q [] (.var x) m :=
  heval.2 _ _ _ (Memory.subsumes_refl _) BigStep.bs_var

/-- `extTouchesFrom A l t`: location `l` is read/written/dropped somewhere in `t`
  at a point where it has not yet been allocated within `t` (its location is not
  in the running allocated set `A`).  An `alloc` extends `A` for the remainder. -/
def Trace.extTouchesFrom : List Nat -> Nat -> Trace -> Prop
| _, _, [] => False
| A, l, (.alloc l' :: t) => Trace.extTouchesFrom (l' :: A) l t
| A, l, (.access _ l' :: t) => (l = l' ∧ l ∉ A) ∨ Trace.extTouchesFrom A l t
| A, l, (.dealloc l' :: t) => (l = l' ∧ l ∉ A) ∨ Trace.extTouchesFrom A l t

/-- `l` is *externally* touched by `t`: accessed or dropped before being
  allocated within `t`.  Such a location is governed by the ambient capability
  set rather than by the trace's own allocations. -/
def Trace.extTouches (t : Trace) (l : Nat) : Prop := Trace.extTouchesFrom [] l t

theorem Trace.extTouchesFrom_append {A : List Nat} {l : Nat} {t1 t2 : Trace}
  (h : Trace.extTouchesFrom A l t1) : Trace.extTouchesFrom A l (t1 ++ t2) := by
  induction t1 generalizing A with
  | nil => simp only [Trace.extTouchesFrom] at h
  | cons it t1 ih =>
    cases it with
    | alloc l' => exact ih h
    | access mu l' =>
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih h)
    | dealloc l' =>
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih h)

/-- Trace-footprint liveness condition for memory subsumption.

  `SubsumeOk m1 t m2` holds when every mutable cell **live in `m1`** that is
  *externally* touched by `t` (read/written/dropped before being allocated within
  `t`) remains **live in `m2`**.  Cells allocated within `t` are exempt — they are
  the trace's own, not governed by the ambient budget — matching `TraceOk`. -/
def Memory.SubsumeOk (m1 : Memory) (t : Trace) (m2 : Memory) : Prop :=
  ∀ l b,
    m1.lookup l = some (.capability (.mcell b .live)) ->
    Trace.extTouches t l ->
    ∃ b', m2.lookup l = some (.capability (.mcell b' .live))

/-- An answer value `BigStep`s to itself with an empty trace. -/
theorem BigStep.of_isAns {m : Memory} {e : Exp {}} (h : e.IsAns) :
    BigStep m e [] e m := by
  cases h with
  | is_var => exact BigStep.bs_var
  | is_val hv =>
    cases hv <;>
      first
        | exact BigStep.bs_pack
        | exact BigStep.bs_val (by constructor)

/-- Progress: a `Safe` configuration reaches at least one `BigStep` answer. -/
theorem Safe.has_answer {m : Memory} {e : Exp {}} (h : Safe m e) :
    ∃ t v m', BigStep m e t v m' := by
  induction h with
  | ans hans => exact ⟨_, _, _, BigStep.of_isAns hans⟩
  | alloc hlk =>
    obtain ⟨l, hfresh⟩ := Memory.exists_fresh _
    exact ⟨_, _, _, BigStep.bs_alloc hlk hfresh⟩
  | apply hlk _ ih =>
    obtain ⟨t, v, m', hbs⟩ := ih
    exact ⟨_, _, _, BigStep.bs_apply hlk hbs⟩
  | invoke hlk1 hlk2 => exact ⟨_, _, _, BigStep.bs_invoke hlk1 hlk2⟩
  | tapply hlk _ ih =>
    obtain ⟨t, v, m', hbs⟩ := ih
    exact ⟨_, _, _, BigStep.bs_tapply hlk hbs⟩
  | capply hlk _ ih =>
    obtain ⟨t, v, m', hbs⟩ := ih
    exact ⟨_, _, _, BigStep.bs_capply hlk hbs⟩
  | unwrap hlk _ ih =>
    obtain ⟨t, v, m', hbs⟩ := ih
    exact ⟨_, _, _, BigStep.bs_unwrap hlk hbs⟩
  | letin _ h_ans _ _ ih1 ih_val ih_var =>
    obtain ⟨t1, v, m1, hbs1⟩ := ih1
    obtain ⟨hsa, hwf1⟩ := h_ans (Memory.subsumes_refl _) hbs1
    cases hsa with
    | is_simple_val hv =>
      obtain ⟨l', hfresh⟩ := Memory.exists_fresh m1
      obtain ⟨t2, v2, m2, hbs2⟩ := ih_val (Memory.subsumes_refl _) hbs1 hv hwf1 l' hfresh
      exact ⟨_, _, _, BigStep.bs_letin_val hbs1 hv hwf1 hfresh hbs2⟩
    | is_var =>
      obtain ⟨t2, v2, m2, hbs2⟩ := ih_var (Memory.subsumes_refl _) hbs1
      exact ⟨_, _, _, BigStep.bs_letin_var hbs1 hbs2⟩
  | unpack _ h_ans _ ih1 ih_val =>
    obtain ⟨t1, v, m1, hbs1⟩ := ih1
    obtain ⟨hpack, hwf1⟩ := h_ans (Memory.subsumes_refl _) hbs1
    cases hpack with
    | pack =>
      obtain ⟨t2, v2, m2, hbs2⟩ := ih_val (Memory.subsumes_refl _) hbs1
      exact ⟨_, _, _, BigStep.bs_unpack hbs1 hbs2⟩
  | read hlk1 hlk2 => exact ⟨_, _, _, BigStep.bs_read hlk1 hlk2⟩
  | write_true hx hy => exact ⟨_, _, _, BigStep.bs_write_true hx hy⟩
  | write_false hx hy => exact ⟨_, _, _, BigStep.bs_write_false hx hy⟩
  | drop hx => exact ⟨_, _, _, BigStep.bs_drop hx⟩
  | cond hres _ _ ih_true ih_false =>
    cases hres with
    | inl hbtrue =>
      obtain ⟨t, v, m', hbs⟩ := ih_true hbtrue
      exact ⟨_, _, _, BigStep.bs_cond_true hbtrue hbs⟩
    | inr hbfalse =>
      obtain ⟨t, v, m', hbs⟩ := ih_false hbfalse
      exact ⟨_, _, _, BigStep.bs_cond_false hbfalse hbs⟩
  | par _ _ ih1 _ =>
    obtain ⟨t, v, m', hbs⟩ := ih1
    exact ⟨_, _, _, BigStep.bs_par_left hbs⟩

/-- Answer existence: every `Eval m e Q` is witnessed by an actual answer — a
  trace `t`, an answer value `e'`, and a memory `m' ⊒ m` with `Q t e' m'`. -/
theorem eval_exists_answer (heval : Eval m e Q) :
  ∃ t e' m', e'.IsAns ∧ m'.subsumes m ∧ Q t e' m' := by
  obtain ⟨hsafe, hpres⟩ := heval
  obtain ⟨t, v, m', hbs⟩ := hsafe.has_answer
  exact ⟨t, v, m', hbs.isAns, hbs.subsumes, hpres t v m' (Memory.subsumes_refl _) hbs⟩

/-- `SubsumeOk` is antitone in the trace: an external touch in a prefix `t1`
  remains an external touch in `t1 ++ t2`. -/
theorem Memory.SubsumeOk.mono_append {m1 m2 : Memory} {t1 t2 : Trace}
  (h : Memory.SubsumeOk m1 (t1 ++ t2) m2) : Memory.SubsumeOk m1 t1 m2 := by
  intro l b hlive htouch
  exact h l b hlive (Trace.extTouchesFrom_append htouch)

/-- An externally-touched location of an `R`-OK trace is covered by `R`: by the
  time it is touched it has not been allocated within the trace, so `TraceOk`'s
  alloc exemption does not apply and `R` must cover it. -/
theorem TraceOkFrom.covers_of_extTouchesFrom {R : CapabilitySet} {l : Nat} :
  ∀ {A : List Nat} {t : Trace},
    TraceOkFrom R A t -> Trace.extTouchesFrom A l t -> ∃ mode, R.covers mode l := by
  intro A t htr
  induction htr with
  | nil => intro htouch; simp only [Trace.extTouchesFrom] at htouch
  | alloc _ ih => intro htouch; exact ih htouch
  | access hcond _ ih =>
    intro htouch
    rcases htouch with ⟨hl, hnotin⟩ | htouch
    · subst hl
      rcases hcond with hcov | hin
      · exact ⟨_, hcov⟩
      · exact absurd hin hnotin
    · exact ih htouch
  | dealloc hcond _ ih =>
    intro htouch
    rcases htouch with ⟨hl, hnotin⟩ | htouch
    · subst hl
      rcases hcond with hcov | hin
      · exact ⟨_, hcov⟩
      · exact absurd hin hnotin
    · exact ih htouch

theorem TraceOk.covers_of_extTouches {R : CapabilitySet} {l : Nat} {t : Trace}
  (htr : TraceOk t R) (htouch : Trace.extTouches t l) : ∃ mode, R.covers mode l :=
  TraceOkFrom.covers_of_extTouchesFrom htr htouch

/-- An externally-*dropped* location of an `R`-OK trace is `.drop`-covered by `R`:
  the dealloc precedes any alloc of the location, so `TraceOk`'s alloc exemption
  does not apply and the `.drop` branch of the `dealloc` clause must hold. -/
theorem TraceOkFrom.drop_covers_of_extDropsFrom {R : CapabilitySet} {l : Nat} :
  ∀ {A : List Nat} {t : Trace},
    TraceOkFrom R A t -> Trace.extDropsFrom A l t -> R.covers .drop l := by
  intro A t htr
  induction htr with
  | nil => intro hd; simp only [Trace.extDropsFrom] at hd
  | alloc _ ih => intro hd; exact ih hd
  | access _ _ ih => intro hd; exact ih hd
  | dealloc hcond _ ih =>
    intro hd
    rcases hd with ⟨hl, hnotin⟩ | hd
    · subst hl
      rcases hcond with hcov | hin
      · exact hcov
      · exact absurd hin hnotin
    · exact ih hd

theorem TraceOk.drop_covers_of_extDrops {R : CapabilitySet} {l : Nat} {t : Trace}
  (htr : TraceOk t R) (hd : Trace.extDrops t l) : R.covers .drop l :=
  TraceOkFrom.drop_covers_of_extDropsFrom htr hd

/-- `is_compatible` transfers across a `FrameLive` step.  For a budget `R` whose
  cells `m` keeps live (`hcompat`) and which are all present in `m` (`hpresent`),
  if `t` externally-drops none of them then they stay live in `m'`.  This is the
  bridge that turns the (missing) frame guarantee into the continuation's
  `is_compatible` obligation in `Fundamental`'s `letin`/`unpack` proofs. -/
theorem Memory.is_compatible_frame {m m' : Memory} {t : Trace} {R : CapabilitySet}
    (hcompat : m.is_compatible R)
    (hpresent : ∀ mu l, R.hasmem mu l -> m.heap l ≠ none)
    (hframe : Memory.FrameLive m t m')
    (hsub : m'.subsumes m)
    (hnodrop : ∀ mu l, R.hasmem mu l -> ¬ Trace.extDrops t l) :
    m'.is_compatible R := by
  intro mu l b ℓ hmem hm1
  cases hcell : m.heap l with
  | none => exact absurd hcell (hpresent mu l hmem)
  | some cell =>
    obtain ⟨v', hv', hsubcell⟩ := hsub l cell hcell
    rw [hv'] at hm1
    injection hm1 with hm1eq
    subst hm1eq
    cases cell with
    | val _ => simp [Cell.subsumes] at hsubcell
    | masked => simp [Cell.subsumes] at hsubcell
    | capability info =>
      cases info with
      | basic => simp [Cell.subsumes] at hsubcell
      | mcell b0 ℓ0 =>
        have hℓ0 : ℓ0 = .live := hcompat mu l b0 ℓ0 hmem hcell
        subst hℓ0
        obtain ⟨b'', hframe'⟩ :=
          hframe l b0 (by rw [Memory.lookup]; exact hcell) (hnodrop mu l hmem)
        rw [Memory.lookup, hv'] at hframe'
        exact (CapabilityInfo.mcell.inj (Cell.capability.inj (Option.some.inj hframe'))).2

/-- The empty trace is `TraceOk` against any capability set. -/
theorem TraceOk.nil {R : CapabilitySet} : TraceOk [] R := TraceOkFrom.nil

/-- A single access event is `TraceOk` when the capability set covers it. -/
theorem TraceOk.access {R : CapabilitySet} {mu : Mutability} {l : Nat}
  (h : R.covers (.access mu) l) : TraceOk [.access mu l] R :=
  TraceOkFrom.access (Or.inl h) TraceOkFrom.nil

/-- A single dealloc event is `TraceOk` when the capability set covers the drop. -/
theorem TraceOk.dealloc {R : CapabilitySet} {l : Nat}
  (h : R.covers .drop l) : TraceOk [.dealloc l] R :=
  TraceOkFrom.dealloc (Or.inl h) TraceOkFrom.nil

/-- A single alloc event is always `TraceOk`: the location is trace-local. -/
theorem TraceOk.alloc {R : CapabilitySet} {l : Nat} : TraceOk [.alloc l] R :=
  TraceOkFrom.alloc TraceOkFrom.nil

/-- `TraceOk` is monotone in the capability set: a larger budget covers every
  access a smaller one does. -/
theorem TraceOkFrom.mono {C C' : CapabilitySet} (hsub : C ⊆ C') :
  ∀ {A : List Nat} {t : Trace}, TraceOkFrom C A t -> TraceOkFrom C' A t := by
  intro A t h
  induction h with
  | nil => exact TraceOkFrom.nil
  | alloc _ ih => exact TraceOkFrom.alloc ih
  | access hcond _ ih =>
    refine TraceOkFrom.access ?_ ih
    rcases hcond with hcov | hin
    · exact Or.inl (CapabilitySet.covers_mono hsub hcov)
    · exact Or.inr hin
  | dealloc hcond _ ih =>
    refine TraceOkFrom.dealloc ?_ ih
    rcases hcond with hcov | hin
    · exact Or.inl (CapabilitySet.covers_mono hsub hcov)
    · exact Or.inr hin

theorem TraceOk.mono {C C' : CapabilitySet} {t : Trace}
  (hsub : C ⊆ C') (h : TraceOk t C) : TraceOk t C' :=
  TraceOkFrom.mono hsub h

/-- `TraceOkFrom` is monotone in the allocated set: enlarging the set of
  trace-local locations only adds exemptions. -/
theorem TraceOkFrom.mono_alloc {C : CapabilitySet} :
  ∀ {A A' : List Nat}, (∀ x, x ∈ A → x ∈ A') → ∀ {t : Trace},
    TraceOkFrom C A t -> TraceOkFrom C A' t := by
  intro A A' hsub t h
  induction h generalizing A' with
  | nil => exact TraceOkFrom.nil
  | alloc _ ih =>
    exact TraceOkFrom.alloc (ih (fun x hx => by
      rcases List.mem_cons.mp hx with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (hsub x h))))
  | access hc _ ih =>
    refine TraceOkFrom.access ?_ (ih hsub)
    rcases hc with h | h
    · exact Or.inl h
    · exact Or.inr (hsub _ h)
  | dealloc hc _ ih =>
    refine TraceOkFrom.dealloc ?_ (ih hsub)
    rcases hc with h | h
    · exact Or.inl h
    · exact Or.inr (hsub _ h)

/-- Concatenating two `TraceOk` traces against the same capability set is
  `TraceOk`: the suffix only gains the prefix's allocations as extra exemptions. -/
theorem TraceOkFrom.append {C : CapabilitySet} :
  ∀ {A : List Nat} {t1 t2 : Trace},
    TraceOkFrom C A t1 -> TraceOkFrom C A t2 -> TraceOkFrom C A (t1 ++ t2) := by
  intro A t1 t2 h1
  induction h1 with
  | nil => intro h2; exact h2
  | alloc _ ih =>
    intro h2
    refine TraceOkFrom.alloc (ih (TraceOkFrom.mono_alloc (fun x hx => ?_) h2))
    exact List.mem_cons.mpr (Or.inr hx)
  | access hc _ ih => intro h2; exact TraceOkFrom.access hc (ih h2)
  | dealloc hc _ ih => intro h2; exact TraceOkFrom.dealloc hc (ih h2)

theorem TraceOk.append {C : CapabilitySet} {t1 t2 : Trace}
  (h1 : TraceOk t1 C) (h2 : TraceOk t2 C) : TraceOk (t1 ++ t2) C :=
  TraceOkFrom.append h1 h2

/-- Downward lookup along subsumption: a cell read in the larger memory `m2`
  is the (subsumer of the) cell at the same location in the smaller `m1`. -/
theorem Memory.lookup_down {m1 m2 : Memory} {x : Nat} {c c0 : Cell}
    (hsub : m2.subsumes m1) (hx1 : m1.lookup x = some c0)
    (hx2 : m2.lookup x = some c) : c.subsumes c0 := by
  obtain ⟨c', hx2', hsubc⟩ := hsub x c0 hx1
  have hx2h : m2.heap x = some c := hx2
  rw [hx2h] at hx2'
  obtain rfl := Option.some.inj hx2'
  exact hsubc

/-- A live mcell in the larger memory `m2` is a (possibly different-bit) live
  mcell at the same location in the smaller `m1` — `Cell.subsumes` only decays
  liveness, so a cell live in `m2` is live in the more-alive `m1`. -/
theorem Memory.mcell_lookup_down {m1 m2 : Memory} {y : Nat} {c0 : Cell} {b : Bool}
    (hsub : m2.subsumes m1) (hy1 : m1.lookup y = some c0)
    (hy2 : m2.lookup y = some (.capability (.mcell b .live))) :
    ∃ b1, m1.lookup y = some (.capability (.mcell b1 .live)) := by
  have h := Memory.lookup_down hsub hy1 hy2
  cases c0 with
  | val => simp only [Cell.subsumes] at h; cases h
  | masked => simp only [Cell.subsumes] at h; cases h
  | capability info =>
    cases info with
    | basic => simp only [Cell.subsumes] at h; cases h
    | mcell b1 ℓ1 =>
      cases ℓ1 with
      | live => exact ⟨b1, hy1⟩
      | dead => simp only [Cell.subsumes] at h; cases h

/-- `resolve` is preserved downward along subsumption at a location that `m1`
  realises: a `.var` resolving to a value in `m2` resolves to the same value in
  `m1` (value cells are preserved by `Cell.subsumes`). -/
theorem resolve_down {m1 m2 : Memory} {x : Nat} {bv : Exp {}}
    (hsub : m2.subsumes m1) (hx1 : m1.heap x ≠ none)
    (hres : resolve m2.heap (.var (.free x)) = some bv) :
    resolve m1.heap (.var (.free x)) = some bv := by
  obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.mp hx1
  simp only [resolve] at hres ⊢
  cases hm2 : m2.heap x with
  | none => rw [hm2] at hres; cases hres
  | some c2 =>
    rw [hm2] at hres
    cases c2 with
    | val hv2 =>
      have hsc : (Cell.val hv2).subsumes c0 := Memory.lookup_down hsub hc0 hm2
      simp only [Cell.subsumes] at hsc
      subst hsc
      rw [hc0]; exact hres
    | capability _ => cases hres
    | masked => cases hres

/- OLD `eval_monotonic` (inductive-`Eval` proof), kept for reference; the
  relational replacement is `eval_monotonic` below.
theorem eval_monotonic_OLD {m1 m2 : Memory}
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
      (by simp [Trace.extTouches, Trace.extTouchesFrom])
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
      (by simp [Trace.extTouches, Trace.extTouchesFrom])
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
      (by simp [Trace.extTouches, Trace.extTouchesFrom])
    apply Eval.eval_write_false (hx := hx2) hy2
    apply hpred
    · constructor
    · exact Memory.update_mcell_subsumes_compat _ _ _ (Exists.intro _ hx) (Exists.intro _ hx2) hsub
    · exact hQ
  case eval_drop hx hQ =>
    obtain ⟨b', hx2⟩ := (hok _ _ _ (Memory.drop_mcell_subsumes _ _ ⟨_, hx⟩) hQ) _ _ hx
      (by simp [Trace.extTouches, Trace.extTouchesFrom])
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
-/

/-- Extending two subsuming memories with equal values at the same fresh
  location preserves subsumption. -/
theorem Memory.extend_val_subsumes_compat {m1 m2 : Memory} {l : Nat}
    {Hv1 Hv2 : HeapVal} (heq : Hv2 = Hv1)
    (w1 : Exp.WfInHeap Hv1.unwrap m1.heap)
    (r1 : Hv1.reachability = compute_reachability m1.heap Hv1.unwrap Hv1.isVal)
    (f1 : m1.heap l = none)
    (w2 : Exp.WfInHeap Hv2.unwrap m2.heap)
    (r2 : Hv2.reachability = compute_reachability m2.heap Hv2.unwrap Hv2.isVal)
    (f2 : m2.heap l = none) (hsub : m2.subsumes m1) :
    (m2.extend_val l Hv2 w2 r2 f2).subsumes (m1.extend_val l Hv1 w1 r1 f1) := by
  subst heq
  change (m2.heap.extend l Hv2).subsumes (m1.heap.extend l Hv2)
  intro l' c hl
  unfold Heap.extend at hl ⊢
  by_cases hn : l' = l
  · subst hn; rw [if_pos rfl] at hl; cases hl
    exact ⟨_, by rw [if_pos rfl], Cell.subsumes_refl _⟩
  · rw [if_neg hn] at hl
    obtain ⟨c', hl', hs⟩ := hsub l' c hl
    exact ⟨c', by rw [if_neg hn]; exact hl', hs⟩

/-- The answer value of an evaluation is well-formed in the final heap. -/
theorem BigStep.wf_answer {m : Memory} {e : Exp {}} {t v m'}
    (hbs : BigStep m e t v m') (hwf : Exp.WfInHeap e m.heap) :
    Exp.WfInHeap v m'.heap := by
  induction hbs with
  | bs_pack => exact hwf
  | bs_val _ => exact hwf
  | bs_var => exact hwf
  | bs_wrap => exact hwf
  | bs_alloc hlk hfresh =>
    exact Exp.WfInHeap.wf_pack
      (CaptureSet.WfInHeap.wf_var_free (Memory.extend_mcell_lookup hfresh))
      (Var.WfInHeap.wf_free (Memory.extend_mcell_lookup hfresh))
  | bs_invoke _ _ => exact Exp.WfInHeap.wf_unit
  | bs_write_true _ _ => exact Exp.WfInHeap.wf_unit
  | bs_write_false _ _ => exact Exp.WfInHeap.wf_unit
  | bs_drop _ => exact Exp.WfInHeap.wf_unit
  | bs_read _ _ => split <;> constructor
  | bs_apply hlk _ ih =>
    cases hwf with
    | wf_app _ hwf_y =>
      apply ih
      obtain ⟨_, _, hwf_e⟩ := Exp.wf_inv_abs (Memory.wf_lookup hlk)
      exact Exp.wf_subst hwf_e (Subst.wf_openVar hwf_y)
  | bs_tapply hlk _ ih =>
    apply ih
    obtain ⟨_, _, hwf_e⟩ := Exp.wf_inv_tabs (Memory.wf_lookup hlk)
    exact Exp.wf_subst hwf_e (Subst.wf_openTVar Ty.WfInHeap.wf_top)
  | bs_capply hlk _ ih =>
    cases hwf with
    | wf_capp _ hwf_cs =>
      apply ih
      obtain ⟨_, _, hwf_e⟩ := Exp.wf_inv_cabs (Memory.wf_lookup hlk)
      exact Exp.wf_subst hwf_e (Subst.wf_openCVar hwf_cs)
  | bs_unwrap hlk _ ih =>
    apply ih
    have hwf_boxed := Memory.wf_lookup hlk
    cases hwf_boxed with
    | wf_boxed _ _ hwf_e => exact hwf_e
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    obtain ⟨_, hwf_e2⟩ := Exp.wf_inv_letin hwf
    apply ih2
    apply Exp.wf_subst
    · exact Exp.wf_monotonic
        (Memory.subsumes_trans
          (Memory.extend_val_subsumes _ _ _ hwf_v rfl hfresh) hbs1.subsumes) hwf_e2
    · exact Subst.wf_openVar (Var.WfInHeap.wf_free
        (Heap.extend_lookup_eq _ _ _))
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    exact ih2 (Exp.wf_subst (Exp.wf_monotonic hbs1.subsumes hwf_e2)
      (match ih1 hwf_e1 with | .wf_var hwf_x => Subst.wf_openVar hwf_x))
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_unpack hwf
    exact ih2 (Exp.wf_subst (Exp.wf_monotonic hbs1.subsumes hwf_e2)
      (match ih1 hwf_e1 with | .wf_pack hwf_cs hwf_x => Subst.wf_unpack hwf_cs hwf_x))
  | bs_cond_true _ _ ih => exact ih (Exp.wf_inv_cond hwf).2.1
  | bs_cond_false _ _ ih => exact ih (Exp.wf_inv_cond hwf).2.2
  | bs_par_left _ ih => exact ih (match hwf with | .wf_par hwf1 _ => hwf1)
  | bs_par_right _ ih => exact ih (match hwf with | .wf_par _ hwf2 => hwf2)

/-- A location holds a **live** mutable cell. -/
def Memory.IsLive (m : Memory) (l : Nat) : Prop :=
  ∃ b, m.lookup l = some (.capability (.mcell b .live))

/-- Locations freshly allocated within a trace. -/
def Trace.allocd : Trace -> Nat -> Prop
| [], _ => False
| (.alloc l' :: t), l => l = l' ∨ Trace.allocd t l
| (.access _ _ :: t), l => Trace.allocd t l
| (.dealloc _ :: t), l => Trace.allocd t l

theorem Trace.allocd_append {t1 t2 : Trace} {l : Nat} :
    Trace.allocd (t1 ++ t2) l ↔ Trace.allocd t1 l ∨ Trace.allocd t2 l := by
  induction t1 with
  | nil => simp [Trace.allocd]
  | cons it t1 ih =>
    cases it <;> simp only [List.cons_append, Trace.allocd, ih, or_assoc]

theorem Memory.extend_mcell_IsLive_self {m : Memory} {l : Nat} {b : Bool} {h} :
    (m.extend_mcell l b h).IsLive l :=
  ⟨b, by simp [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell]⟩

theorem Memory.extend_mcell_IsLive_ne {m : Memory} {l0 : Nat} {b : Bool} {h} {l : Nat}
    (hne : l ≠ l0) : (m.extend_mcell l0 b h).IsLive l ↔ m.IsLive l := by
  simp only [Memory.IsLive, Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hne]

theorem Memory.update_mcell_IsLive_self {m : Memory} {x : Nat} {b : Bool} {h} :
    (m.update_mcell x b .live h).IsLive x :=
  ⟨b, by simp [Memory.lookup, Memory.update_mcell, Heap.update_cell]⟩

theorem Memory.update_mcell_IsLive_ne {m : Memory} {x : Nat} {b : Bool} {ℓ} {h} {l : Nat}
    (hne : l ≠ x) : (m.update_mcell x b ℓ h).IsLive l ↔ m.IsLive l := by
  simp only [Memory.IsLive, Memory.lookup, Memory.update_mcell, Heap.update_cell, if_neg hne]

theorem Memory.drop_mcell_not_IsLive_self {m : Memory} {x : Nat} {h} :
    ¬ (m.drop_mcell x h).IsLive x := by
  rintro ⟨b, hb⟩
  simp [Memory.lookup, Memory.drop_mcell, Heap.update_cell] at hb

theorem Memory.drop_mcell_IsLive_ne {m : Memory} {x : Nat} {h} {l : Nat}
    (hne : l ≠ x) : (m.drop_mcell x h).IsLive l ↔ m.IsLive l := by
  simp only [Memory.IsLive, Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_neg hne]

-- "Agree" lemmas: a memory operation applied to two memories that agree on `l`'s
-- liveness yields memories that still agree on `l` — the location-`by_cases` is
-- internalized so `simulate_down`'s cases needn't name the operated location.
theorem Memory.extend_mcell_IsLive_agree {m1 m2 : Memory} {L : Nat} {b1 b2 : Bool}
    {h1 h2} {l : Nat} (hag : m1.IsLive l ↔ m2.IsLive l) :
    (m1.extend_mcell L b1 h1).IsLive l ↔ (m2.extend_mcell L b2 h2).IsLive l := by
  by_cases hl : l = L
  · subst hl
    exact iff_of_true Memory.extend_mcell_IsLive_self Memory.extend_mcell_IsLive_self
  · rw [Memory.extend_mcell_IsLive_ne hl, Memory.extend_mcell_IsLive_ne hl]; exact hag

theorem Memory.update_mcell_IsLive_agree {m1 m2 : Memory} {x : Nat} {b1 b2 : Bool}
    {h1 h2} {l : Nat} (hag : m1.IsLive l ↔ m2.IsLive l) :
    (m1.update_mcell x b1 .live h1).IsLive l ↔ (m2.update_mcell x b2 .live h2).IsLive l := by
  by_cases hl : l = x
  · subst hl
    exact iff_of_true Memory.update_mcell_IsLive_self Memory.update_mcell_IsLive_self
  · rw [Memory.update_mcell_IsLive_ne hl, Memory.update_mcell_IsLive_ne hl]; exact hag

theorem Memory.drop_mcell_IsLive_agree {m1 m2 : Memory} {x : Nat} {h1 h2} {l : Nat}
    (hag : m1.IsLive l ↔ m2.IsLive l) :
    (m1.drop_mcell x h1).IsLive l ↔ (m2.drop_mcell x h2).IsLive l := by
  by_cases hl : l = x
  · subst hl
    exact iff_of_false Memory.drop_mcell_not_IsLive_self Memory.drop_mcell_not_IsLive_self
  · rw [Memory.drop_mcell_IsLive_ne hl, Memory.drop_mcell_IsLive_ne hl]; exact hag

theorem Memory.extend_val_not_IsLive_self {m : Memory} {l : Nat} {v hwf hreach hfresh} :
    ¬ (m.extend_val l v hwf hreach hfresh).IsLive l := by
  rintro ⟨b, hb⟩
  simp [Memory.lookup, Memory.extend_val, Heap.extend] at hb

theorem Memory.extend_val_IsLive_ne {m : Memory} {l0 : Nat} {v hwf hreach hfresh} {l : Nat}
    (hne : l ≠ l0) : (m.extend_val l0 v hwf hreach hfresh).IsLive l ↔ m.IsLive l := by
  simp only [Memory.IsLive, Memory.lookup, Memory.extend_val, Heap.extend, if_neg hne]

/-- A location allocated within a `BigStep`'s trace was absent from the initial
  memory (allocation is always fresh). -/
theorem BigStep.alloc_fresh {m : Memory} {e : Exp {}} {t v m' l}
    (hbs : BigStep m e t v m') (ha : Trace.allocd t l) : m.lookup l = none := by
  induction hbs with
  | bs_pack | bs_val _ | bs_var | bs_wrap | bs_invoke _ _ | bs_read _ _
  | bs_write_true _ _ | bs_write_false _ _ | bs_drop _ => simp [Trace.allocd] at ha
  | bs_alloc _ hfresh => simp only [Trace.allocd, or_false] at ha; subst ha; exact hfresh
  | bs_apply _ _ ih | bs_tapply _ _ ih | bs_capply _ _ ih | bs_unwrap _ _ ih
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih | bs_par_left _ ih
  | bs_par_right _ ih => exact ih ha
  | bs_letin_val hbs1 hv hwf hfresh hbs2 ih1 ih2 =>
    rcases Trace.allocd_append.mp ha with h1 | h2
    · exact ih1 h1
    · exact Heap.none_of_subsumes_none
        (Memory.subsumes_trans (Memory.extend_val_subsumes _ _ _ hwf rfl hfresh)
          hbs1.subsumes) (ih2 h2)
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    rcases Trace.allocd_append.mp ha with h1 | h2
    · exact ih1 h1
    · exact Heap.none_of_subsumes_none hbs1.subsumes (ih2 h2)
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    rcases Trace.allocd_append.mp ha with h1 | h2
    · exact ih1 h1
    · exact Heap.none_of_subsumes_none hbs1.subsumes (ih2 h2)

/-- `extDropsFrom` only consults the alloc-set through `l`-membership. -/
theorem Trace.extDropsFrom_mem_irrel {l : Nat} :
    ∀ {t : Trace} {A A' : List Nat}, (l ∈ A ↔ l ∈ A') ->
      (Trace.extDropsFrom A l t ↔ Trace.extDropsFrom A' l t) := by
  intro t
  induction t with
  | nil => intro A A' _; rfl
  | cons it t ih =>
    intro A A' hmem
    cases it with
    | alloc l' => exact ih (by simp only [List.mem_cons, hmem])
    | access _ _ => exact ih hmem
    | dealloc l' =>
      simp only [Trace.extDropsFrom]
      rw [ih hmem]
      constructor
      · rintro (⟨he, hn⟩ | hr)
        · exact Or.inl ⟨he, fun h => hn (hmem.mpr h)⟩
        · exact Or.inr hr
      · rintro (⟨he, hn⟩ | hr)
        · exact Or.inl ⟨he, fun h => hn (hmem.mp h)⟩
        · exact Or.inr hr

/-- A drop in the prefix is a drop in the whole. -/
theorem Trace.extDropsFrom_append_left {l : Nat} :
    ∀ {t1 t2 : Trace} {A : List Nat},
      Trace.extDropsFrom A l t1 -> Trace.extDropsFrom A l (t1 ++ t2) := by
  intro t1
  induction t1 with
  | nil => intro t2 A h; simp only [Trace.extDropsFrom] at h
  | cons it t1 ih =>
    intro t2 A h
    cases it with
    | alloc l' => exact ih h
    | access _ _ => exact ih h
    | dealloc l' =>
      rcases h with hd | hr
      · exact Or.inl hd
      · exact Or.inr (ih hr)

/-- A drop of a non-prefix-allocated location in the suffix is a drop in the whole. -/
theorem Trace.extDropsFrom_append_right {l : Nat} :
    ∀ {t1 t2 : Trace} {A : List Nat}, ¬ Trace.allocd t1 l -> l ∉ A ->
      Trace.extDropsFrom A l t2 -> Trace.extDropsFrom A l (t1 ++ t2) := by
  intro t1
  induction t1 with
  | nil => intro t2 A _ _ h; exact h
  | cons it t1 ih =>
    intro t2 A hna hnA h
    cases it with
    | alloc l' =>
      simp only [Trace.allocd, not_or] at hna
      refine ih hna.2 (by simp only [List.mem_cons, not_or]; exact ⟨hna.1, hnA⟩) ?_
      exact (Trace.extDropsFrom_mem_irrel
        (by simp only [List.mem_cons]; exact ⟨Or.inr, fun hb => hb.resolve_left hna.1⟩)).mp h
    | access _ _ => exact ih hna hnA h
    | dealloc l' => exact Or.inr (ih hna hnA h)

/-- `FrameLive` composes across trace concatenation, provided the prefix does not
  allocate the live cells (true for a `BigStep` from `m`, by `alloc_fresh`). -/
theorem Memory.FrameLive.append {m m1 m2 : Memory} {t1 t2 : Trace}
    (h1 : Memory.FrameLive m t1 m1) (h2 : Memory.FrameLive m1 t2 m2)
    (hfresh : ∀ l b, m.lookup l = some (.capability (.mcell b .live)) -> ¬ Trace.allocd t1 l) :
    Memory.FrameLive m (t1 ++ t2) m2 := by
  intro l b hlive hnd
  have hna := hfresh l b hlive
  have hnd1 : ¬ Trace.extDrops t1 l := fun h => hnd (Trace.extDropsFrom_append_left h)
  have hnd2 : ¬ Trace.extDrops t2 l := fun h =>
    hnd (Trace.extDropsFrom_append_right hna (by simp) h)
  obtain ⟨b', hb'⟩ := h1 l b hlive hnd1
  exact h2 l b' hb' hnd2

-- Lookup-equality helpers for the memory operations (used by `live_appears_allocd`).
theorem Memory.extend_mcell_lookup_eq_base_of_ne {m : Memory} {L : Nat} {b h} {l : Nat} {c}
    (hl' : (m.extend_mcell L b h).lookup l = some c) (hl : m.lookup l = none) : l = L := by
  by_contra hne
  rw [show (m.extend_mcell L b h).lookup l = m.lookup l from by
    simp [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hne], hl] at hl'
  simp at hl'

theorem Memory.update_mcell_lookup_ne {m : Memory} {x : Nat} {b ℓ h} {l : Nat} (hne : l ≠ x) :
    (m.update_mcell x b ℓ h).lookup l = m.lookup l := by
  simp [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_neg hne]

theorem Memory.drop_mcell_lookup_ne {m : Memory} {x : Nat} {h} {l : Nat} (hne : l ≠ x) :
    (m.drop_mcell x h).lookup l = m.lookup l := by
  simp [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_neg hne]

theorem Memory.update_mcell_lookup_none {m : Memory} {x : Nat} {b ℓ h} {l : Nat}
    (hl : m.lookup l = none) (hx : ∃ c, m.lookup x = some c) :
    (m.update_mcell x b ℓ h).lookup l = none := by
  by_cases hlx : l = x
  · subst hlx; obtain ⟨c, hc⟩ := hx; rw [hc] at hl; simp at hl
  · rw [Memory.update_mcell_lookup_ne hlx]; exact hl

theorem Memory.drop_mcell_lookup_none {m : Memory} {x : Nat} {h} {l : Nat}
    (hl : m.lookup l = none) (hx : ∃ c, m.lookup x = some c) :
    (m.drop_mcell x h).lookup l = none := by
  by_cases hlx : l = x
  · subst hlx; obtain ⟨c, hc⟩ := hx; rw [hc] at hl; simp at hl
  · rw [Memory.drop_mcell_lookup_ne hlx]; exact hl

theorem Memory.extend_val_lookup_ne {m : Memory} {L : Nat} {v h1 h2 h3} {l : Nat} (hne : l ≠ L) :
    (m.extend_val L v h1 h2 h3).lookup l = m.lookup l := by
  simp [Memory.lookup, Memory.extend_val, Heap.extend, if_neg hne]

theorem Memory.extend_val_lookup_self {m : Memory} {L : Nat} {v h1 h2 h3} :
    (m.extend_val L v h1 h2 h3).lookup L = some (.val v) := by
  simp [Memory.lookup, Memory.extend_val, Heap.extend]

theorem Memory.extend_val_lookup_mcell {m : Memory} {L : Nat} {v h1 h2 h3} {l : Nat} {b ℓ}
    (hl' : (m.extend_val L v h1 h2 h3).lookup l = some (.capability (.mcell b ℓ))) :
    m.lookup l = some (.capability (.mcell b ℓ)) := by
  by_cases hlL : l = L
  · subst hlL; rw [Memory.extend_val_lookup_self] at hl'; simp at hl'
  · rwa [Memory.extend_val_lookup_ne hlL] at hl'

/-- `extTouchesFrom` only consults the alloc-set through `l`-membership. -/
theorem Trace.extTouchesFrom_mem_irrel {l : Nat} :
    ∀ {t : Trace} {A A' : List Nat}, (l ∈ A ↔ l ∈ A') ->
      (Trace.extTouchesFrom A l t ↔ Trace.extTouchesFrom A' l t) := by
  intro t
  induction t with
  | nil => intro A A' _; rfl
  | cons it t ih =>
    intro A A' hmem
    cases it with
    | alloc l' => exact ih (by simp only [List.mem_cons, hmem])
    | access _ l' =>
      simp only [Trace.extTouchesFrom]
      rw [ih hmem]
      constructor
      · rintro (⟨he, hn⟩ | hr)
        · exact Or.inl ⟨he, fun h => hn (hmem.mpr h)⟩
        · exact Or.inr hr
      · rintro (⟨he, hn⟩ | hr)
        · exact Or.inl ⟨he, fun h => hn (hmem.mp h)⟩
        · exact Or.inr hr
    | dealloc l' =>
      simp only [Trace.extTouchesFrom]
      rw [ih hmem]
      constructor
      · rintro (⟨he, hn⟩ | hr)
        · exact Or.inl ⟨he, fun h => hn (hmem.mpr h)⟩
        · exact Or.inr hr
      · rintro (⟨he, hn⟩ | hr)
        · exact Or.inl ⟨he, fun h => hn (hmem.mp h)⟩
        · exact Or.inr hr

/-- An external touch in the suffix (of a non-prefix-allocated location) is an
  external touch in the whole. -/
theorem Trace.extTouchesFrom_append_right {l : Nat} :
    ∀ {t1 t2 : Trace} {A : List Nat}, ¬ Trace.allocd t1 l -> l ∉ A ->
      Trace.extTouchesFrom A l t2 -> Trace.extTouchesFrom A l (t1 ++ t2) := by
  intro t1
  induction t1 with
  | nil => intro t2 A _ _ h; exact h
  | cons it t1 ih =>
    intro t2 A hna hnA h
    cases it with
    | alloc l' =>
      simp only [Trace.allocd, not_or] at hna
      refine ih hna.2 (by simp only [List.mem_cons, not_or]; exact ⟨hna.1, hnA⟩) ?_
      exact (Trace.extTouchesFrom_mem_irrel
        (by simp only [List.mem_cons]; exact ⟨Or.inr, fun hb => hb.resolve_left hna.1⟩)).mp h
    | access _ l' => exact Or.inr (ih hna hnA h)
    | dealloc l' => exact Or.inr (ih hna hnA h)

/-- A location holding a **live** mcell after a `BigStep`, absent before, was
  freshly allocated within the trace.  (Live mcells arise only from `alloc`;
  `letin` bindings produce value cells, not mcells — handled by
  `extend_val_lookup_mcell`.) -/
theorem BigStep.live_appears_allocd {m : Memory} {e : Exp {}} {t v m' l b}
    (hbs : BigStep m e t v m') (hl : m.lookup l = none)
    (hl' : m'.lookup l = some (.capability (.mcell b .live))) : Trace.allocd t l := by
  induction hbs generalizing b with
  | bs_pack | bs_val _ | bs_var | bs_wrap | bs_invoke _ _ | bs_read _ _ =>
    rw [hl] at hl'; simp at hl'
  | bs_alloc _ hfresh =>
    have heq := Memory.extend_mcell_lookup_eq_base_of_ne hl' hl
    subst heq; simp [Trace.allocd]
  | bs_write_true hx _ | bs_write_false hx _ =>
    rw [Memory.update_mcell_lookup_none hl ⟨_, hx⟩] at hl'; simp at hl'
  | bs_drop hx =>
    rw [Memory.drop_mcell_lookup_none hl ⟨_, hx⟩] at hl'; simp at hl'
  | bs_apply _ _ ih | bs_tapply _ _ ih | bs_capply _ _ ih | bs_unwrap _ _ ih
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih | bs_par_left _ ih | bs_par_right _ ih =>
    exact ih hl hl'
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    rename_i _ _ _ _ _ _ m1 _ vval l'
    refine Trace.allocd_append.mpr ?_
    rcases hsrc : (m1.extend_val l' ⟨vval, hv, compute_reachability m1.heap vval hv⟩
        hwf_v rfl hfresh).lookup l with _ | c
    · exact Or.inr (ih2 hsrc hl')
    · obtain ⟨b1, hc'⟩ := Memory.mcell_lookup_down hbs2.subsumes hsrc hl'
      exact Or.inl (ih1 hl (Memory.extend_val_lookup_mcell hc'))
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    rename_i _ _ _ _ _ _ m1 _ _
    refine Trace.allocd_append.mpr ?_
    rcases hsrc : m1.lookup l with _ | c
    · exact Or.inr (ih2 hsrc hl')
    · obtain ⟨b1, hc'⟩ := Memory.mcell_lookup_down hbs2.subsumes hsrc hl'
      exact Or.inl (ih1 hl hc')
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    rename_i _ _ _ _ _ _ m1 _ _ _
    refine Trace.allocd_append.mpr ?_
    rcases hsrc : m1.lookup l with _ | c
    · exact Or.inr (ih2 hsrc hl')
    · obtain ⟨b1, hc'⟩ := Memory.mcell_lookup_down hbs2.subsumes hsrc hl'
      exact Or.inl (ih1 hl hc')

/-- Safety lifts upward along subsumption: if `e` is safe from `m1` and every
  touched cell stays live in `m2` (`hok`, fed `m1`'s answers via `hpres`), then
  `e` is safe from `m2`. -/
theorem Safe.lift {m1 : Memory} {e : Exp {}} {Q : Tpost} (hsafe : Safe m1 e)
    (hsub : m2.subsumes m1)
    (hpres : ∀ t v m', BigStep m1 e t v m' -> Q t v m')
    (hok : ∀ t v m, m.subsumes m1 -> Q t v m -> Memory.SubsumeOk m1 t m2)
    (hwf : Exp.WfInHeap e m1.heap) : Safe m2 e := by
  induction hsafe generalizing m2 Q with
  | ans hans => exact Safe.ans hans
  | alloc hlk =>
    obtain ⟨_, hx2, hsubx⟩ := hsub _ _ hlk
    simp only [Cell.subsumes] at hsubx; subst hsubx
    exact Safe.alloc hx2
  | invoke hlkx hlky =>
    obtain ⟨_, hx2, hsubx⟩ := hsub _ _ hlkx
    obtain ⟨_, hy2, hsuby⟩ := hsub _ _ hlky
    simp only [Cell.subsumes] at hsubx hsuby; subst hsubx; subst hsuby
    exact Safe.invoke hx2 hy2
  | apply hlk _ ih =>
    obtain ⟨_, hx2, hsubx⟩ := hsub _ _ hlk
    simp only [Cell.subsumes] at hsubx; subst hsubx
    match hwf with
    | .wf_app _ hwfy =>
      obtain ⟨_, _, he⟩ := Exp.wf_inv_abs (Memory.wf_lookup hlk)
      exact Safe.apply hx2 (ih hsub (fun t v m' hbs => hpres t v m' (BigStep.bs_apply hlk hbs))
        hok (Exp.wf_subst he (Subst.wf_openVar hwfy)))
  | tapply hlk _ ih =>
    obtain ⟨_, hx2, hsubx⟩ := hsub _ _ hlk
    simp only [Cell.subsumes] at hsubx; subst hsubx
    obtain ⟨_, _, he⟩ := Exp.wf_inv_tabs (Memory.wf_lookup hlk)
    exact Safe.tapply hx2 (ih hsub (fun t v m' hbs => hpres t v m' (BigStep.bs_tapply hlk hbs))
      hok (Exp.wf_subst he (Subst.wf_openTVar Ty.WfInHeap.wf_top)))
  | capply hlk _ ih =>
    obtain ⟨_, hx2, hsubx⟩ := hsub _ _ hlk
    simp only [Cell.subsumes] at hsubx; subst hsubx
    match hwf with
    | .wf_capp _ hcs =>
      obtain ⟨_, _, he⟩ := Exp.wf_inv_cabs (Memory.wf_lookup hlk)
      exact Safe.capply hx2 (ih hsub (fun t v m' hbs => hpres t v m' (BigStep.bs_capply hlk hbs))
        hok (Exp.wf_subst he (Subst.wf_openCVar hcs)))
  | unwrap hlk _ ih =>
    obtain ⟨_, hx2, hsubx⟩ := hsub _ _ hlk
    simp only [Cell.subsumes] at hsubx; subst hsubx
    exact Safe.unwrap hx2 (ih hsub (fun t v m' hbs => hpres t v m' (BigStep.bs_unwrap hlk hbs))
      hok (match Memory.wf_lookup hlk with | .wf_boxed _ _ he => he))
  | read hlkx hlky =>
    obtain ⟨_, hx2, hsubx⟩ := hsub _ _ hlkx
    simp only [Cell.subsumes] at hsubx; subst hsubx
    have hsubok := hok _ _ _ (Memory.subsumes_refl _)
      (hpres _ _ _ (BigStep.bs_read hlkx hlky))
    obtain ⟨_, hy2⟩ := hsubok _ _ hlky (by simp [Trace.extTouches, Trace.extTouchesFrom])
    exact Safe.read hx2 hy2
  | write_true hlkx hlky =>
    obtain ⟨_, hy2, hsuby⟩ := hsub _ _ hlky
    simp only [Cell.subsumes] at hsuby; subst hsuby
    have hsubok := hok _ _ _ (Memory.update_mcell_subsumes _ _ _ _ ⟨_, hlkx⟩)
      (hpres _ _ _ (BigStep.bs_write_true hlkx hlky))
    obtain ⟨_, hx2⟩ := hsubok _ _ hlkx (by simp [Trace.extTouches, Trace.extTouchesFrom])
    exact Safe.write_true hx2 hy2
  | write_false hlkx hlky =>
    obtain ⟨_, hy2, hsuby⟩ := hsub _ _ hlky
    simp only [Cell.subsumes] at hsuby; subst hsuby
    have hsubok := hok _ _ _ (Memory.update_mcell_subsumes _ _ _ _ ⟨_, hlkx⟩)
      (hpres _ _ _ (BigStep.bs_write_false hlkx hlky))
    obtain ⟨_, hx2⟩ := hsubok _ _ hlkx (by simp [Trace.extTouches, Trace.extTouchesFrom])
    exact Safe.write_false hx2 hy2
  | drop hlkx =>
    have hsubok := hok _ _ _ (Memory.drop_mcell_subsumes _ _ ⟨_, hlkx⟩)
      (hpres _ _ _ (BigStep.bs_drop hlkx))
    obtain ⟨_, hx2⟩ := hsubok _ _ hlkx (by simp [Trace.extTouches, Trace.extTouchesFrom])
    exact Safe.drop hx2
  | cond hres h_true h_false ih_true ih_false =>
    obtain ⟨_, hwf2, hwf3⟩ := Exp.wf_inv_cond hwf
    refine Safe.cond (hres.imp (resolve_monotonic hsub) (resolve_monotonic hsub)) ?_ ?_
    · intro hb2
      cases hres with
      | inl hb1 =>
        exact ih_true hb1 hsub
          (fun t v m' hbs => hpres t v m' (BigStep.bs_cond_true hb1 hbs)) hok hwf2
      | inr hbf => rw [resolve_monotonic hsub hbf] at hb2; simp at hb2
    · intro hb2
      cases hres with
      | inl hbt => rw [resolve_monotonic hsub hbt] at hb2; simp at hb2
      | inr hb1 =>
        exact ih_false hb1 hsub
          (fun t v m' hbs => hpres t v m' (BigStep.bs_cond_false hb1 hbs)) hok hwf3
  | par _ _ ih1 ih2 =>
    match hwf with
    | .wf_par hwf1 hwf2 =>
      exact Safe.par
        (ih1 hsub (fun t v m' hbs => hpres t v m' (BigStep.bs_par_left hbs)) hok hwf1)
        (ih2 hsub (fun t v m' hbs => hpres t v m' (BigStep.bs_par_right hbs)) hok hwf2)
  | letin _ h_ans h_val h_var ih1 ih_val ih_var =>
    clear ih_val ih_var m1
    rename_i e1 e2 m1 _
    obtain ⟨hwf_e1, _⟩ := Exp.wf_inv_letin hwf
    -- `hok` for `e1`: run the continuation to a `letin`-answer, apply the outer
    -- `hok` to the full run, and restrict the footprint back to `t` via `mono_append`.
    have hok_e1 : ∀ t v m, m.subsumes m1 -> BigStep m1 e1 t v m ->
        Memory.SubsumeOk m1 t m2 := by
      intro t v m _ hbs1
      obtain ⟨hsa, hwf_v⟩ := h_ans (Memory.subsumes_refl _) hbs1
      cases hsa with
      | is_simple_val hv =>
        obtain ⟨lf, hfreshf⟩ := Memory.exists_fresh m
        obtain ⟨t2, v2, mf, hbs2⟩ :=
          (h_val (Memory.subsumes_refl _) hbs1 hv hwf_v lf hfreshf).has_answer
        have hfull := BigStep.bs_letin_val hbs1 hv hwf_v hfreshf hbs2
        exact (hok _ _ _ hfull.subsumes (hpres _ _ _ hfull)).mono_append
      | is_var =>
        obtain ⟨t2, v2, mf, hbs2⟩ := (h_var (Memory.subsumes_refl _) hbs1).has_answer
        have hfull := BigStep.bs_letin_var hbs1 hbs2
        exact (hok _ _ _ hfull.subsumes (hpres _ _ _ hfull)).mono_append
    -- With the robust heads, the `m2`-side continuations are just `m1`'s heads at
    -- a further-subsuming `m0` (`subsumes_trans`); no `simulate_down` is needed.
    exact Safe.letin
      (ih1 (Q := fun t v m => BigStep m1 e1 t v m) hsub (fun _ _ _ h => h) hok_e1 hwf_e1)
      (fun hs hbs => h_ans (Memory.subsumes_trans hs hsub) hbs)
      (fun hs hbs hv hwfv l' hf => h_val (Memory.subsumes_trans hs hsub) hbs hv hwfv l' hf)
      (fun hs hbs => h_var (Memory.subsumes_trans hs hsub) hbs)
  | unpack _ h_ans h_val ih1 ih_val =>
    clear ih_val m1
    rename_i e1 e2 m1 _
    obtain ⟨hwf_e1, _⟩ := Exp.wf_inv_unpack hwf
    have hok_e1 : ∀ t v m, m.subsumes m1 -> BigStep m1 e1 t v m ->
        Memory.SubsumeOk m1 t m2 := by
      intro t v m _ hbs1
      obtain ⟨hpk, hwf_v⟩ := h_ans (Memory.subsumes_refl _) hbs1
      cases hpk with
      | pack =>
        obtain ⟨t2, v2, mf, hbs2⟩ := (h_val (Memory.subsumes_refl _) hbs1).has_answer
        have hfull := BigStep.bs_unpack hbs1 hbs2
        exact (hok _ _ _ hfull.subsumes (hpres _ _ _ hfull)).mono_append
    exact Safe.unpack
      (ih1 (Q := fun t v m => BigStep m1 e1 t v m) hsub (fun _ _ _ h => h) hok_e1 hwf_e1)
      (fun hs hbs => h_ans (Memory.subsumes_trans hs hsub) hbs)
      (fun hs hbs => h_val (Memory.subsumes_trans hs hsub) hbs)

/-- Memory-subsumption monotonicity of `Eval`.  With FAITHFUL reads this is sound
  because `Eval`'s preservation is **robust over `m0 ⊒ m`**: a run from any
  `m0 ⊒ m2` is a run from `m0 ⊒ m1` (transitivity), so both parts reduce to the
  `m1`-side.  `hpred`/`hbool` are no longer needed here — `is_bool_independent`
  does its work downstream (the denotation discharges the robust obligation).
  `hok` is still consumed by `Safe.lift` (trace-footprint liveness). -/
theorem eval_monotonic {m1 m2 : Memory}
  (_hpred : Q.is_monotonic)
  (_hbool : Q.is_bool_independent)
  (hsub : m2.subsumes m1)
  (hok : ∀ t v m, m.subsumes m1 -> Q t v m -> Memory.SubsumeOk m1 t m2)
  (hwf : Exp.WfInHeap e m1.heap)
  (heval : Eval m1 e Q) :
  Eval m2 e Q := by
  obtain ⟨hsafe1, hpres1⟩ := heval
  refine ⟨hsafe1.lift hsub (fun t v m' hbs => hpres1 t v m' (Memory.subsumes_refl _) hbs)
    hok hwf, ?_⟩
  intro m0 t v m' hsub0 hbs
  exact hpres1 t v m' (Memory.subsumes_trans hsub0 hsub) hbs

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
  -- Safety is postcondition-independent, so it carries verbatim; the answer
  -- predicate is weakened along `himp` (each answer memory subsumes the start,
  -- hence subsumes `m` by transitivity through the robust `m0 ⊒ m`).
  obtain ⟨hsafe, hpres⟩ := heval
  refine ⟨hsafe, ?_⟩
  intro m0 t v m' hsub0 hbs
  exact himp m' (Memory.subsumes_trans hbs.subsumes hsub0) t v (hpres t v m' hsub0 hbs)

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
