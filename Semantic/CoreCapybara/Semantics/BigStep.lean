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
  (h_ans : ∀ t1 v m1, BigStep m e1 t1 v m1 -> v.IsSimpleAns ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {t1 : Trace} {m1} {v : Exp {}},
    BigStep m e1 t1 v m1 -> (hv : Exp.IsSimpleVal v) -> (hwf_v : Exp.WfInHeap v m1.heap) ->
    ∀ l' (hfresh : m1.lookup l' = none),
      Safe (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
        (e2.subst (Subst.openVar (.free l')))) ->
  (h_var : ∀ {t1 : Trace} {m1} {x : Var .var {}},
    BigStep m e1 t1 (.var x) m1 -> Safe m1 (e2.subst (Subst.openVar x))) ->
  Safe m (.letin e1 e2)
| unpack {m : Memory} :
  Safe m e1 ->
  (h_ans : ∀ t1 v m1, BigStep m e1 t1 v m1 -> v.IsPack ∧ Exp.WfInHeap v m1.heap) ->
  (h_val : ∀ {t1 : Trace} {m1} {x : Var .var {}} {cs : CaptureSet {}},
    BigStep m e1 t1 (.pack cs x) m1 -> Safe m1 (e2.subst (Subst.unpack cs x))) ->
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
  Safety is bundled in, so this is no weaker than the old inductive `Eval`. -/
def Eval (m : Memory) (e : Exp {}) (Q : Tpost) : Prop :=
  Safe m e ∧ (∀ t v m', BigStep m e t v m' -> Q t v m')

/-- `Eval` on a variable does not change memory and emits no events: the only
    rule producing `Eval m (.var x) Q` is `eval_var`. -/
theorem Eval.var_inv {m : Memory} {x : Var .var {}} {Q : Tpost}
    (heval : Eval m (.var x) Q) : Q [] (.var x) m := by
  cases heval with
  | eval_val hv _ => cases hv
  | eval_var hQ => exact hQ

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
