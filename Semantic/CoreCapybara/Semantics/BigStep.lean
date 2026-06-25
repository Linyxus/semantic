import Semantic.CoreCapybara.Syntax
import Semantic.CoreCapybara.Substitution
import Semantic.CoreCapybara.Semantics.Heap
import Semantic.CoreCapybara.Semantics.SmallStep

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

/-- Relational big-step evaluation.  `BigStep m e t v m'` holds when evaluating
  `e` from memory `m` terminates at value `v` and final memory `m'`, recording
  the trace `t` of heap events.

  The intermediate result of a `letin`/`unpack` is an *actual* answer (`m1` is a
  genuine `e1`-result), so the continuation can observe a live budget. -/
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
| bs_read {m : Memory} {x : Nat} {b b' : Bool} :
  m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩) ->
  m.lookup y = some (.capability (.mcell b .live)) ->
  -- The result bit `b'` is nondeterministic, independent of the stored bit `b`: a
  -- `read` uses the capability (emit `.access y`; requires `y` live) and yields some
  -- `Bool`, abstracting the value at the type system's abstraction boundary (it tracks
  -- effects/capabilities/capture/liveness, never bool data). Faithful execution is the
  -- instance `b' = b`, so faithful runs ⊆ these runs and soundness transfers. Covering
  -- both outcomes is what makes `Eval` Kripke-monotone: `Cell.subsumes` ignores the
  -- mcell bit, so `m2 ⊒ m1` may flip a live cell, and a stored-bit read would break
  -- `eval_monotonic`.
  BigStep m (.read (.free x)) [.access .ro y] (if b' then .btrue else .bfalse) m
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
| bs_par {m m1 m2 : Memory} {v1 v2 : Exp {}} :
  BigStep m e1 t1 v1 m1 ->
  BigStep m1 e2 t2 v2 m2 ->
  BigStep m (.par C1 C2 e1 e2) (t1 ++ t2) .unit m2

/-- Locations `t` ACCESSES or DEALLOCATES (i.e. that appear as a non-`alloc`
  trace event).  Every such location is a capability cell at the time of the
  event (see `BigStep.trace_cells_cap`). -/
def Trace.touched : Trace -> Nat -> Prop
| [], _ => False
| (.access _ l' :: t), l => l = l' ∨ Trace.touched t l
| (.dealloc l' :: t), l => l = l' ∨ Trace.touched t l
| (.alloc _ :: t), l => Trace.touched t l

theorem Trace.touched_append {t1 t2 : Trace} {l : Nat} :
    Trace.touched (t1 ++ t2) l <-> Trace.touched t1 l ∨ Trace.touched t2 l := by
  induction t1 with
  | nil => simp [Trace.touched]
  | cons it t1 ih =>
    cases it <;> simp only [List.cons_append, Trace.touched, ih, or_assoc]

/-- `extTouchesFromMode A l cm t`: location `l` is externally touched by `t` — read,
  written, or dropped at a point where it has not yet been allocated within `t`
  (its location is not in the running allocated set `A`) — **with capability mode
  `cm`** (`.access mu` for a read/write of mutability `mu`; `.drop` for a dealloc).
  The mode-carrying refinement of `extTouchesFrom`; an `alloc` extends `A`. -/
def Trace.extTouchesFromMode : List Nat -> Nat -> CapMode -> Trace -> Prop
| _, _, _, [] => False
| A, l, cm, (.alloc l' :: t) => Trace.extTouchesFromMode (l' :: A) l cm t
| A, l, cm, (.access mu l' :: t) =>
    (l = l' ∧ l ∉ A ∧ cm = .access mu) ∨ Trace.extTouchesFromMode A l cm t
| A, l, cm, (.dealloc l' :: t) =>
    (l = l' ∧ l ∉ A ∧ cm = .drop) ∨ Trace.extTouchesFromMode A l cm t

/-- `l` is externally touched by `t` with mode `cm`: accessed (`cm = .access mu`)
  or dropped (`cm = .drop`) before being allocated within `t`.  Such a location is
  governed by the ambient capability set, not by `t`'s own allocations — so a cell
  `t` allocates itself is NEVER externally touched by `t`. -/
def Trace.extTouchesMode (t : Trace) (l : Nat) (cm : CapMode) : Prop :=
  Trace.extTouchesFromMode [] l cm t

/-- **Trace non-interference.**  Two traces do not interfere when every location
  they BOTH touch *externally* is read-only on both sides: if `t1` externally
  touches `l` with mode `cm1` and `t2` externally touches `l` with mode `cm2`,
  then `cm1 = cm2 = .access .ro`.  Concurrent reads of a shared cell are fine; a
  write or drop by either branch on a shared external cell is a conflict.

  The *external* qualifier is what makes this sound: a cell a branch allocates
  itself is private — never externally touched by that branch — so two branches
  that each `alloc`-then-mutate a fresh cell do NOT interfere, even if their runs
  happen to pick the same location index.  (A plain mutates/touches formulation
  would wrongly flag that as a conflict.)

  The type system discharges it from `Noninterference` of the branches' budgets:
  a shared external touch with mode `cm` is `covers cm`-ed by that branch's budget,
  and `Noninterference.shared_ro` forces the two covering members to `.access .ro`,
  hence both `cm`s to `.access .ro`. -/
def Trace.Noninterfere (t1 t2 : Trace) : Prop :=
  ∀ l cm1 cm2,
    Trace.extTouchesMode t1 l cm1 → Trace.extTouchesMode t2 l cm2 →
      cm1 = .access .ro ∧ cm2 = .access .ro

/-- Progress / safety predicate: `Safe m e` means evaluating `e` from `m` never
  gets stuck — every redex reached is reducible, and (inductively, as a least fixed
  point) every path reaches an answer.

  The `letin`/`unpack` continuations quantify over the actual `BigStep` answers of
  the head, so the intermediate `m1` is a genuine result. -/
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
| par {m : Memory} {C1 C2 : CapabilitySet} {Cs1 Cs2 : CaptureSet {}} :
  -- Each branch independently safe at the current memory: the separation content
  -- needed to schedule the right branch before the left has finished.
  Safe m e1 ->
  Safe m e2 ->
  -- Sequential continuation: after `e1` runs to an answer, `e2` is safe at the result.
  (h2 : ∀ {t1 : Trace} {v1 : Exp {}} {m1}, BigStep m e1 t1 v1 m1 -> Safe m1 e2) ->
  -- Robust budget bounds: every run of a branch from any `m' ⊒ m` has its trace bounded
  -- by that branch's budget `Cᵢ`. `Cᵢ` is growable (left abstract here), absorbing a
  -- branch's own fresh allocations into the reduct's budget via `capsOf`.
  (hb1 : ∀ {m' : Memory} {t : Trace} {v : Exp {}} {m''},
    m'.subsumes m -> Exp.WfInHeap e1 m'.heap -> BigStep m' e1 t v m'' -> TraceOk t C1) ->
  (hb2 : ∀ {m' : Memory} {t : Trace} {v : Exp {}} {m''},
    m'.subsumes m -> Exp.WfInHeap e2 m'.heap -> BigStep m' e2 t v m'' -> TraceOk t C2) ->
  -- Robust branch safety: each branch is safe from any `m' ⊒ m` compatible with its
  -- budget. Memory-monotone, so `Safe.lift` preserves it.
  (hrs1 : ∀ {m' : Memory}, m'.subsumes m -> m'.is_compatible C1 -> Safe m' e1) ->
  (hrs2 : ∀ {m' : Memory}, m'.subsumes m -> m'.is_compatible C2 -> Safe m' e2) ->
  -- Budget presence: each branch's budget references only cells present in `m`.
  (hpres1 : ∀ mu l, C1.hasmem mu l -> m.heap l ≠ none) ->
  (hpres2 : ∀ mu l, C2.hasmem mu l -> m.heap l ≠ none) ->
  -- Budget = annotation reachability (mutual `⊆`): the abstract budget `Cᵢ` tracks the
  -- annotation `Csᵢ`'s reachability, maintained as both grow in lockstep (budget by
  -- `capsOf`, annotation by `growByAllocs`).
  (hcov1 : C1 ⊆ Cs1.reachability m ∧ Cs1.reachability m ⊆ C1) ->
  (hcov2 : C2 ⊆ Cs2.reachability m ∧ Cs2.reachability m ⊆ C2) ->
  -- The two budgets are non-interfering (`SepCheck`): with the bounds this yields trace
  -- non-interference for any pair of branch runs (`traceOk_noninterfere`).
  (hni : CapabilitySet.Noninterference C1 C2) ->
  Safe m (.par Cs1 Cs2 e1 e2)

/-- Trace-observing evaluation predicate: `e` from `m` is **safe** (never stuck —
  `Safe m e`) **and** every answer it reaches satisfies `Q`. -/
def Eval (m : Memory) (e : Exp {}) (Q : Tpost) : Prop :=
  Safe m e ∧ (∀ t v m', BigStep m e t v m' -> Q t v m')

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
  | bs_par _ _ _ _ => exact Exp.IsAns.is_val Exp.IsVal.unit

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
  | bs_par _ _ ih1 ih2 => exact Memory.subsumes_trans ih2 ih1

/-- `Eval` on a variable does not change memory and emits no events: the only
    `BigStep` answer of `.var x` is `(.var x)` itself with an empty trace. -/
theorem Eval.var_inv {m : Memory} {x : Var .var {}} {Q : Tpost}
    (heval : Eval m (.var x) Q) : Q [] (.var x) m :=
  heval.2 _ _ _ BigStep.bs_var

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

/-- An external touch is in particular a touch (forgetting the alloc-exclusion). -/
theorem Trace.touched_of_extTouchesFrom {A : List Nat} {l : Nat} :
    ∀ {t : Trace}, Trace.extTouchesFrom A l t -> Trace.touched t l := by
  intro t
  induction t generalizing A with
  | nil => intro h; simp only [Trace.extTouchesFrom] at h
  | cons it t ih =>
    cases it with
    | alloc l' => intro h; exact ih h
    | access mu l' => intro h; rcases h with ⟨hl, _⟩ | h
                      · exact Or.inl hl
                      · exact Or.inr (ih h)
    | dealloc l' => intro h; rcases h with ⟨hl, _⟩ | h
                    · exact Or.inl hl
                    · exact Or.inr (ih h)

theorem Trace.touched_of_extTouches {t : Trace} {l : Nat}
    (h : Trace.extTouches t l) : Trace.touched t l :=
  Trace.touched_of_extTouchesFrom h

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

/-- An answer's only `BigStep` run is the trivial self-run: empty trace, the value
  is the answer itself, memory unchanged.  (Answers are normal forms.) -/
theorem BigStep.isAns_inv {m : Memory} {e : Exp {}} {t v m'}
    (hbs : BigStep m e t v m') (hans : e.IsAns) : t = [] ∧ v = e ∧ m' = m := by
  cases hbs <;>
    first
      | exact ⟨rfl, rfl, rfl⟩
      | (cases hans with | is_val hv => cases hv)

/-- A fresh location avoiding a given finite set `S` (and the current domain). -/
theorem Memory.exists_fresh_avoiding (m : Memory) (S : Finset Nat) :
    ∃ l : Nat, l ∉ S ∧ m.lookup l = none := by
  obtain ⟨dom, hdom⟩ := m.findom
  refine ⟨(dom ∪ S).sup id + 1, ?_, ?_⟩
  · intro hin
    have hle : (dom ∪ S).sup id + 1 ≤ (dom ∪ S).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_right dom hin)
    omega
  · unfold Memory.lookup
    by_contra h
    have hmem : (dom ∪ S).sup id + 1 ∈ dom := (hdom _).mp h
    have hle : (dom ∪ S).sup id + 1 ≤ (dom ∪ S).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left S hmem)
    omega

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
    obtain ⟨hsa, hwf1⟩ := h_ans _ _ _ hbs1
    cases hsa with
    | is_simple_val hv =>
      obtain ⟨l', hfresh⟩ := Memory.exists_fresh m1
      obtain ⟨t2, v2, m2, hbs2⟩ := ih_val hbs1 hv hwf1 l' hfresh
      exact ⟨_, _, _, BigStep.bs_letin_val hbs1 hv hwf1 hfresh hbs2⟩
    | is_var =>
      obtain ⟨t2, v2, m2, hbs2⟩ := ih_var hbs1
      exact ⟨_, _, _, BigStep.bs_letin_var hbs1 hbs2⟩
  | unpack _ h_ans _ ih1 ih_val =>
    obtain ⟨t1, v, m1, hbs1⟩ := ih1
    obtain ⟨hpack, hwf1⟩ := h_ans _ _ _ hbs1
    cases hpack with
    | pack =>
      obtain ⟨t2, v2, m2, hbs2⟩ := ih_val hbs1
      exact ⟨_, _, _, BigStep.bs_unpack hbs1 hbs2⟩
  | read hlk1 hlk2 => exact ⟨_, _, _, BigStep.bs_read (b' := true) hlk1 hlk2⟩
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
  | par _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ ih2 _ _ =>
    obtain ⟨t1, v1, m1, hbs1⟩ := ih1
    obtain ⟨t2, v2, m2, hbs2⟩ := ih2 hbs1
    exact ⟨_, _, _, BigStep.bs_par hbs1 hbs2⟩

/-- Answer existence: every `Eval m e Q` is witnessed by an actual answer — a
  trace `t`, an answer value `e'`, and a memory `m' ⊒ m` with `Q t e' m'`. -/
theorem eval_exists_answer (heval : Eval m e Q) :
  ∃ t e' m', e'.IsAns ∧ m'.subsumes m ∧ Q t e' m' := by
  obtain ⟨hsafe, hpres⟩ := heval
  obtain ⟨t, v, m', hbs⟩ := hsafe.has_answer
  exact ⟨t, v, m', hbs.isAns, hbs.subsumes, hpres t v m' hbs⟩

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

/-- An externally-touched location, with the mode of the touch, is covered by the
  ambient budget at that very mode (mode-carrying refinement of
  `drop_covers_of_extDropsFrom`).  Used to discharge `Trace.Noninterfere` from the
  budgets' `Noninterference`. -/
theorem TraceOkFrom.covers_of_extTouchesFromMode {R : CapabilitySet} {l : Nat} {cm : CapMode} :
  ∀ {A : List Nat} {t : Trace},
    TraceOkFrom R A t -> Trace.extTouchesFromMode A l cm t -> R.covers cm l := by
  intro A t htr
  induction htr with
  | nil => intro ht; simp only [Trace.extTouchesFromMode] at ht
  | alloc _ ih => intro ht; exact ih ht
  | access hcond _ ih =>
    intro ht
    rcases ht with ⟨hl, hnotin, hcm⟩ | ht
    · subst hl; subst hcm
      rcases hcond with hcov | hin
      · exact hcov
      · exact absurd hin hnotin
    · exact ih ht
  | dealloc hcond _ ih =>
    intro ht
    rcases ht with ⟨hl, hnotin, hcm⟩ | ht
    · subst hl; subst hcm
      rcases hcond with hcov | hin
      · exact hcov
      · exact absurd hin hnotin
    · exact ih ht

theorem TraceOk.covers_of_extTouchesMode {R : CapabilitySet} {l : Nat} {cm : CapMode}
  {t : Trace} (htr : TraceOk t R) (ht : Trace.extTouchesMode t l cm) : R.covers cm l :=
  TraceOkFrom.covers_of_extTouchesFromMode htr ht

/-- If two non-interfering budgets both have a member at the same location, both
  members are `.access .ro` (read-only).  This is the core consequence of
  `Noninterference`. -/
theorem CapabilitySet.Noninterference.shared_ro
    {C1 C2 : CapabilitySet} {mu1 mu2 : CapMode} {l : Nat}
    (hni : CapabilitySet.Noninterference C1 C2)
    (h1 : C1.hasmem mu1 l) (h2 : C2.hasmem mu2 l) :
    mu1 = .access .ro ∧ mu2 = .access .ro := by
  induction hni generalizing mu1 mu2 with
  | ni_symm _ ih =>
    obtain ⟨ha, hb⟩ := ih h2 h1
    exact ⟨hb, ha⟩
  | ni_empty => cases h1
  | ni_union _ _ ih1 ih2 =>
    cases h1 with
    | left h => exact ih1 h h2
    | right h => exact ih2 h h2
  | ni_ro =>
    cases h1
    cases h2
    exact ⟨rfl, rfl⟩
  | ni_disj hne =>
    cases h1
    cases h2
    exact absurd rfl hne

/-- A capability mode below `.access .ro` IS `.access .ro` (`.ro` is the minimal
  access mutability, and `.drop` is incomparable to any access). -/
theorem CapMode.le_access_ro_eq {cm : CapMode} (h : cm ≤ CapMode.access .ro) :
    cm = .access .ro := by
  cases h with
  | access hmu => cases hmu with | refl => rfl

/-- **Discharge of `Trace.Noninterfere` from the budgets.**  If `t1`/`t2` are
  `TraceOk` for non-interfering budgets `C1`/`C2`, their traces are
  non-interfering: a location both externally touch is `covers`-ed by both
  budgets, and `Noninterference.shared_ro` forces both covering members — hence
  both touch modes — to `.access .ro`.  This is the operational image of `SepCheck`
  used by `Safe.par`/`eval_par`/`sem_typ_par`. -/
theorem traceOk_noninterfere {C1 C2 : CapabilitySet} {t1 t2 : Trace}
    (h1 : TraceOk t1 C1) (h2 : TraceOk t2 C2)
    (hni : CapabilitySet.Noninterference C1 C2) :
    Trace.Noninterfere t1 t2 := by
  intro l cm1 cm2 hext1 hext2
  obtain ⟨mu1, hmem1, hle1⟩ :=
    CapabilitySet.covers_imp_exists_hasmem (h1.covers_of_extTouchesMode hext1)
  obtain ⟨mu2, hmem2, hle2⟩ :=
    CapabilitySet.covers_imp_exists_hasmem (h2.covers_of_extTouchesMode hext2)
  obtain ⟨hro1, hro2⟩ := hni.shared_ro hmem1 hmem2
  subst hro1; subst hro2
  exact ⟨CapMode.le_access_ro_eq hle1, CapMode.le_access_ro_eq hle2⟩

/-- `is_compatible` transfers across a `FrameLive` step.  For a budget `R` whose
  cells `m` keeps live (`hcompat`) and which are all present in `m` (`hpresent`),
  if `t` externally-drops none of them then they stay live in `m'`.  Yields the
  continuation's `is_compatible` obligation in `Fundamental`'s `letin`/`unpack`. -/
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
  | bs_par _ _ _ _ => exact Exp.WfInHeap.wf_unit

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

/-- Locations freshly allocated within a trace, as a `List` (for `TraceOkFrom`'s
  allocated-set argument). -/
def Trace.allocList : Trace -> List Nat
| [] => []
| (.alloc l' :: t) => l' :: Trace.allocList t
| (.access _ _ :: t) => Trace.allocList t
| (.dealloc _ :: t) => Trace.allocList t

theorem Trace.mem_allocList {t : Trace} {l : Nat} :
    l ∈ Trace.allocList t ↔ Trace.allocd t l := by
  induction t with
  | nil => simp [Trace.allocList, Trace.allocd]
  | cons it t ih =>
    cases it <;> simp only [Trace.allocList, Trace.allocd, List.mem_cons, ih]

/-- Sequential append: running `t1` (which collects its allocations) and then `t2`
  with those allocations available as exemptions yields `TraceOk` for `t1 ++ t2`.
  Unlike `TraceOkFrom.append`, the suffix `t2` may touch cells `t1` allocated. -/
theorem TraceOkFrom.append_seq {C : CapabilitySet} :
  ∀ {A : List Nat} {t1 t2 : Trace},
    TraceOkFrom C A t1 -> TraceOkFrom C (Trace.allocList t1 ++ A) t2 ->
    TraceOkFrom C A (t1 ++ t2) := by
  intro A t1 t2 h1
  induction h1 with
  | nil => intro h2; exact h2
  | alloc _ ih =>
    intro h2
    refine TraceOkFrom.alloc (ih ?_)
    refine TraceOkFrom.mono_alloc (fun x hx => ?_) h2
    simp only [Trace.allocList, List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
    tauto
  | access hc _ ih => intro h2; exact TraceOkFrom.access hc (ih h2)
  | dealloc hc _ ih => intro h2; exact TraceOkFrom.dealloc hc (ih h2)

/-- Budget-translate with an extra exemption set `S`.  The re-bucketing hypothesis
  is required only at TOUCHED locations (those `t` actually accesses/deallocates) —
  the proof only consults it at events — which lets the caller discharge it from the
  `BigStep` run (`trace_cells_cap`: touched cells are capabilities) instead of from a
  global "all covered cells" fact. -/
theorem TraceOkFrom.translate {C C' : CapabilitySet} {S : List Nat} :
  ∀ {A : List Nat} {t : Trace},
    TraceOkFrom C A t ->
    (∀ mode l, Trace.touched t l -> C.covers mode l -> C'.covers mode l ∨ l ∈ S) ->
    TraceOkFrom C' (A ++ S) t := by
  intro A t h
  induction h with
  | nil => intro _; exact TraceOkFrom.nil
  | alloc _ ih => intro htr; exact TraceOkFrom.alloc (ih htr)
  | access hc _ ih =>
    intro htr
    refine TraceOkFrom.access ?_ (ih (fun mode l htch hcov => htr mode l (Or.inr htch) hcov))
    rcases hc with hcov | hin
    · rcases htr _ _ (Or.inl rfl) hcov with hc' | hs
      · exact Or.inl hc'
      · exact Or.inr (List.mem_append.mpr (Or.inr hs))
    · exact Or.inr (List.mem_append.mpr (Or.inl hin))
  | dealloc hc _ ih =>
    intro htr
    refine TraceOkFrom.dealloc ?_ (ih (fun mode l htch hcov => htr mode l (Or.inr htch) hcov))
    rcases hc with hcov | hin
    · rcases htr _ _ (Or.inl rfl) hcov with hc' | hs
      · exact Or.inl hc'
      · exact Or.inr (List.mem_append.mpr (Or.inr hs))
    · exact Or.inr (List.mem_append.mpr (Or.inl hin))

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
-- liveness yields memories that still agree on `l` (location-`by_cases` internalized).
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

/-- Downward simulation: an evaluation from the larger memory `m2` is replayed
  from the smaller `m1` with the SAME trace and value, ending at a subsumed
  memory.  Cells touched by `m2`'s run are live in `m2`, hence live in the more-
  alive `m1` (`Cell.subsumes` only decays liveness); `e`'s free locations are in
  `m1` (`hwf`), with value cells preserved.  A `read` picks the SAME result bit
  in `m1` — possible exactly because `bs_read` is bit-nondeterministic.

  The third conjunct is a **liveness bisimulation**: for any cell whose liveness
  agrees between the two bases (or which is allocated within `t`), the two runs
  agree on its final liveness.  This is what lets the safety lift (`Safe.lift`)
  carry the continuation past `e1`'s freshly-allocated cells. -/
theorem BigStep.simulate_down {m2 : Memory} {e : Exp {}} {t : Trace} {v : Exp {}}
    {m2' : Memory} (hbs : BigStep m2 e t v m2') :
    ∀ {m1 : Memory}, m2.subsumes m1 -> Exp.WfInHeap e m1.heap ->
      ∃ m1', BigStep m1 e t v m1' ∧ m2'.subsumes m1' ∧
        ∀ l, ((m1.IsLive l ↔ m2.IsLive l) ∨ Trace.allocd t l) ->
          (m1'.IsLive l ↔ m2'.IsLive l) := by
  induction hbs with
  | bs_pack =>
    intro m1 hsub _
    exact ⟨m1, BigStep.bs_pack, hsub, fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_val hv =>
    intro m1 hsub _
    exact ⟨m1, BigStep.bs_val hv, hsub, fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_var =>
    intro m1 hsub _
    exact ⟨m1, BigStep.bs_var, hsub, fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_wrap =>
    intro m1 hsub _
    exact ⟨m1, BigStep.bs_wrap, hsub, fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_alloc hlk hfresh =>
    intro m1 hsub hwf
    match hwf with
    | .wf_alloc (.wf_free hx1) =>
      have hcx := Memory.lookup_down hsub hx1 hlk
      simp only [Cell.subsumes] at hcx
      subst hcx
      have hfresh1 : m1.heap _ = none := Heap.none_of_subsumes_none hsub hfresh
      refine ⟨_, BigStep.bs_alloc hx1 hfresh1,
        Memory.extend_mcell_subsumes_compat _ _ hfresh1 hfresh hsub, ?_⟩
      intro l h
      rcases h with hag | ha
      · exact Memory.extend_mcell_IsLive_agree hag
      · simp only [Trace.allocd, or_false] at ha; subst ha
        exact iff_of_true Memory.extend_mcell_IsLive_self Memory.extend_mcell_IsLive_self
  | bs_invoke hlkx hlky =>
    intro m1 hsub hwf
    match hwf with
    | .wf_app (.wf_free hx1) (.wf_free hy1) =>
      have hcx := Memory.lookup_down hsub hx1 hlkx
      have hcy := Memory.lookup_down hsub hy1 hlky
      simp only [Cell.subsumes] at hcx hcy
      subst hcx; subst hcy
      exact ⟨m1, BigStep.bs_invoke hx1 hy1, hsub,
        fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_apply hlk hbody ih =>
    intro m1 hsub hwf
    match hwf with
    | .wf_app (.wf_free hx1) hwfy =>
      have hcx := Memory.lookup_down hsub hx1 hlk
      simp only [Cell.subsumes] at hcx
      subst hcx
      obtain ⟨_, _, he⟩ := Exp.wf_inv_abs (Memory.wf_lookup hx1)
      obtain ⟨m1', hbs1', hsub', hlive'⟩ := ih hsub (Exp.wf_subst he (Subst.wf_openVar hwfy))
      exact ⟨m1', BigStep.bs_apply hx1 hbs1', hsub', hlive'⟩
  | bs_tapply hlk hbody ih =>
    intro m1 hsub hwf
    match hwf with
    | .wf_tapp (.wf_free hx1) _ =>
      have hcx := Memory.lookup_down hsub hx1 hlk
      simp only [Cell.subsumes] at hcx
      subst hcx
      obtain ⟨_, _, he⟩ := Exp.wf_inv_tabs (Memory.wf_lookup hx1)
      obtain ⟨m1', hbs1', hsub', hlive'⟩ :=
        ih hsub (Exp.wf_subst he (Subst.wf_openTVar Ty.WfInHeap.wf_top))
      exact ⟨m1', BigStep.bs_tapply hx1 hbs1', hsub', hlive'⟩
  | bs_capply hlk hbody ih =>
    intro m1 hsub hwf
    match hwf with
    | .wf_capp (.wf_free hx1) hcs =>
      have hcx := Memory.lookup_down hsub hx1 hlk
      simp only [Cell.subsumes] at hcx
      subst hcx
      obtain ⟨_, _, he⟩ := Exp.wf_inv_cabs (Memory.wf_lookup hx1)
      obtain ⟨m1', hbs1', hsub', hlive'⟩ := ih hsub (Exp.wf_subst he (Subst.wf_openCVar hcs))
      exact ⟨m1', BigStep.bs_capply hx1 hbs1', hsub', hlive'⟩
  | bs_unwrap hlk hbody ih =>
    intro m1 hsub hwf
    match hwf with
    | .wf_unwrap (.wf_free hx1) =>
      have hcx := Memory.lookup_down hsub hx1 hlk
      simp only [Cell.subsumes] at hcx
      subst hcx
      obtain ⟨m1', hbs1', hsub', hlive'⟩ := ih hsub
        (match Memory.wf_lookup hx1 with | .wf_boxed _ _ he => he)
      exact ⟨m1', BigStep.bs_unwrap hx1 hbs1', hsub', hlive'⟩
  | bs_read hlkx hlky =>
    intro m1 hsub hwf
    match hwf with
    | .wf_read (.wf_free hx1) =>
      have hcx := Memory.lookup_down hsub hx1 hlkx
      simp only [Cell.subsumes] at hcx
      subst hcx
      obtain ⟨b1, hy1⟩ := (match Memory.wf_lookup hx1 with
        | .wf_reader (.wf_free hy0) => Memory.mcell_lookup_down hsub hy0 hlky)
      exact ⟨m1, BigStep.bs_read hx1 hy1, hsub,
        fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_write_true hlkx hlky =>
    intro m1 hsub hwf
    match hwf with
    | .wf_write (.wf_free hx1) (.wf_free hy1) =>
      obtain ⟨b1, hx1'⟩ := Memory.mcell_lookup_down hsub hx1 hlkx
      have hcy := Memory.lookup_down hsub hy1 hlky
      simp only [Cell.subsumes] at hcy
      subst hcy
      exact ⟨_, BigStep.bs_write_true hx1' hy1,
        Memory.update_mcell_subsumes_compat _ _ _ ⟨b1, hx1'⟩ ⟨_, hlkx⟩ hsub,
        fun l h => Memory.update_mcell_IsLive_agree (h.resolve_right (by simp [Trace.allocd]))⟩
  | bs_write_false hlkx hlky =>
    intro m1 hsub hwf
    match hwf with
    | .wf_write (.wf_free hx1) (.wf_free hy1) =>
      obtain ⟨b1, hx1'⟩ := Memory.mcell_lookup_down hsub hx1 hlkx
      have hcy := Memory.lookup_down hsub hy1 hlky
      simp only [Cell.subsumes] at hcy
      subst hcy
      exact ⟨_, BigStep.bs_write_false hx1' hy1,
        Memory.update_mcell_subsumes_compat _ _ _ ⟨b1, hx1'⟩ ⟨_, hlkx⟩ hsub,
        fun l h => Memory.update_mcell_IsLive_agree (h.resolve_right (by simp [Trace.allocd]))⟩
  | bs_drop hlkx =>
    intro m1 hsub hwf
    match hwf with
    | .wf_drop (.wf_free hx1) =>
      obtain ⟨b1, hx1'⟩ := Memory.mcell_lookup_down hsub hx1 hlkx
      exact ⟨_, BigStep.bs_drop hx1',
        Memory.drop_mcell_subsumes_compat _ ⟨b1, hx1'⟩ ⟨_, hlkx⟩ hsub,
        fun l h => Memory.drop_mcell_IsLive_agree (h.resolve_right (by simp [Trace.allocd]))⟩
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    intro m1 hsub hwf
    rename_i _ _ _ _ _ _ _ _ w l
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    obtain ⟨m1_1, hbs1', hsub1', hlive1⟩ := ih1 hsub hwf_e1
    have hwf_v1 := BigStep.wf_answer hbs1' hwf_e1
    have hfresh1 := Heap.none_of_subsumes_none hsub1' hfresh
    obtain ⟨m1', hbs2', hsub2', hlive2⟩ :=
      ih2 (m1 := m1_1.extend_val l ⟨w, hv, compute_reachability m1_1.heap w hv⟩
            hwf_v1 rfl hfresh1)
        (Memory.extend_val_subsumes_compat
          (by rw [compute_reachability_monotonic hsub1' _ hv hwf_v1])
          hwf_v1 rfl hfresh1 hwf_v rfl hfresh hsub1')
        (Exp.wf_subst
          (Exp.wf_monotonic
            (Heap.subsumes_trans (Heap.extend_subsumes hfresh1) (BigStep.subsumes hbs1'))
            hwf_e2)
          (Subst.wf_openVar (Var.WfInHeap.wf_free (Heap.extend_lookup_eq _ _ _))))
    refine ⟨m1', BigStep.bs_letin_val hbs1' hv hwf_v1 hfresh1 hbs2', hsub2', ?_⟩
    intro lc h
    apply hlive2
    by_cases hlc : lc = l
    · subst hlc
      exact Or.inl (iff_of_false Memory.extend_val_not_IsLive_self
        Memory.extend_val_not_IsLive_self)
    · rcases h with hag | ha
      · exact Or.inl (by simp only [Memory.extend_val_IsLive_ne hlc]; exact hlive1 lc (Or.inl hag))
      · rcases Trace.allocd_append.mp ha with h1 | h2
        · exact Or.inl (by simp only [Memory.extend_val_IsLive_ne hlc]; exact hlive1 lc (Or.inr h1))
        · exact Or.inr h2
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    intro m1 hsub hwf
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    obtain ⟨m1_1, hbs1', hsub1', hlive1⟩ := ih1 hsub hwf_e1
    have hwf_body := Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes hbs1') hwf_e2)
      (match BigStep.wf_answer hbs1' hwf_e1 with
        | Exp.WfInHeap.wf_var hx => Subst.wf_openVar hx)
    obtain ⟨m1', hbs2', hsub2', hlive2⟩ := ih2 hsub1' hwf_body
    refine ⟨m1', BigStep.bs_letin_var hbs1' hbs2', hsub2', ?_⟩
    intro lc h
    rcases h with hag | ha
    · exact hlive2 lc (Or.inl (hlive1 lc (Or.inl hag)))
    · rcases Trace.allocd_append.mp ha with h1 | h2
      · exact hlive2 lc (Or.inl (hlive1 lc (Or.inr h1)))
      · exact hlive2 lc (Or.inr h2)
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    intro m1 hsub hwf
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_unpack hwf
    obtain ⟨m1_1, hbs1', hsub1', hlive1⟩ := ih1 hsub hwf_e1
    have hwf_body := Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes hbs1') hwf_e2)
      (match BigStep.wf_answer hbs1' hwf_e1 with
        | Exp.WfInHeap.wf_pack hcs hx => Subst.wf_unpack hcs hx)
    obtain ⟨m1', hbs2', hsub2', hlive2⟩ := ih2 hsub1' hwf_body
    refine ⟨m1', BigStep.bs_unpack hbs1' hbs2', hsub2', ?_⟩
    intro lc h
    rcases h with hag | ha
    · exact hlive2 lc (Or.inl (hlive1 lc (Or.inl hag)))
    · rcases Trace.allocd_append.mp ha with h1 | h2
      · exact hlive2 lc (Or.inl (hlive1 lc (Or.inr h1)))
      · exact hlive2 lc (Or.inr h2)
  | bs_cond_true hres hbody ih =>
    intro m1 hsub hwf
    obtain ⟨hwfx, hwf2, _⟩ := Exp.wf_inv_cond hwf
    obtain ⟨m1', hbs1', hsub', hlive'⟩ := ih hsub hwf2
    refine ⟨m1', BigStep.bs_cond_true ?_ hbs1', hsub', hlive'⟩
    match hwfx with
    | .wf_free h => exact resolve_down hsub (Option.ne_none_iff_exists'.mpr ⟨_, h⟩) hres
  | bs_cond_false hres hbody ih =>
    intro m1 hsub hwf
    obtain ⟨hwfx, _, hwf3⟩ := Exp.wf_inv_cond hwf
    obtain ⟨m1', hbs1', hsub', hlive'⟩ := ih hsub hwf3
    refine ⟨m1', BigStep.bs_cond_false ?_ hbs1', hsub', hlive'⟩
    match hwfx with
    | .wf_free h => exact resolve_down hsub (Option.ne_none_iff_exists'.mpr ⟨_, h⟩) hres
  | bs_par hbs1 hbs2 ih1 ih2 =>
    intro m1 hsub hwf
    cases hwf with
    | wf_par _ _ hwf_e1 hwf_e2 =>
      obtain ⟨m1_1, hbs1', hsub1', hlive1⟩ := ih1 hsub hwf_e1
      obtain ⟨m1', hbs2', hsub2', hlive2⟩ :=
        ih2 hsub1' (Exp.wf_monotonic (BigStep.subsumes hbs1') hwf_e2)
      refine ⟨m1', BigStep.bs_par hbs1' hbs2', hsub2', ?_⟩
      intro lc h
      rcases h with hag | ha
      · exact hlive2 lc (Or.inl (hlive1 lc (Or.inl hag)))
      · rcases Trace.allocd_append.mp ha with h1 | h2
        · exact hlive2 lc (Or.inl (hlive1 lc (Or.inr h1)))
        · exact hlive2 lc (Or.inr h2)

/-- A location allocated within a `BigStep`'s trace was absent from the initial
  memory (allocation is always fresh). -/
theorem BigStep.alloc_fresh {m : Memory} {e : Exp {}} {t v m' l}
    (hbs : BigStep m e t v m') (ha : Trace.allocd t l) : m.lookup l = none := by
  induction hbs with
  | bs_pack | bs_val _ | bs_var | bs_wrap | bs_invoke _ _ | bs_read _ _
  | bs_write_true _ _ | bs_write_false _ _ | bs_drop _ => simp [Trace.allocd] at ha
  | bs_alloc _ hfresh => simp only [Trace.allocd, or_false] at ha; subst ha; exact hfresh
  | bs_apply _ _ ih | bs_tapply _ _ ih | bs_capply _ _ ih | bs_unwrap _ _ ih
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih => exact ih ha
  | bs_par hbs1 _ ih1 ih2 =>
    rcases Trace.allocd_append.mp ha with h1 | h2
    · exact ih1 h1
    · exact Heap.none_of_subsumes_none hbs1.subsumes (ih2 h2)
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

/-- A CAPABILITY found in `m.extend_val …` was already in `m` (the added cell is a
  non-capability val). -/
theorem Memory.extend_val_lookup_cap {m : Memory} {L : Nat} {v h1 h2 h3} {l : Nat} {c}
    (hl' : (m.extend_val L v h1 h2 h3).lookup l = some (.capability c)) :
    m.lookup l = some (.capability c) := by
  by_cases hlL : l = L
  · subst hlL; rw [Memory.extend_val_lookup_self] at hl'; simp at hl'
  · rwa [Memory.extend_val_lookup_ne hlL] at hl'

/-- A run that never TOUCHES (reads/writes/drops) a pre-existing cell `c` leaves
  `c`'s lookup unchanged.  (`c` is not allocated either — it already exists, and
  allocation is fresh.)  The per-cell frame fact underlying the diamond. -/
theorem BigStep.untouched_preserved {m : Memory} {e : Exp {}} {t v m' : _} {c : Nat}
    (hbs : BigStep m e t v m') :
    m.lookup c ≠ none → ¬ Trace.touched t c → m'.lookup c = m.lookup c := by
  induction hbs with
  | bs_pack | bs_val _ | bs_var | bs_wrap | bs_invoke _ _ | bs_read _ _ =>
    intro _ _; rfl
  | bs_alloc _ hfresh =>
    intro hc _
    have hne : c ≠ _ := fun h => hc (h ▸ hfresh)
    simp [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hne]
  | bs_write_true hx _ =>
    intro _ hnt
    exact Memory.update_mcell_lookup_ne (fun h => hnt (Or.inl h))
  | bs_write_false hx _ =>
    intro _ hnt
    exact Memory.update_mcell_lookup_ne (fun h => hnt (Or.inl h))
  | bs_drop hx =>
    intro _ hnt
    exact Memory.drop_mcell_lookup_ne (fun h => hnt (Or.inl h))
  | bs_apply _ _ ih | bs_tapply _ _ ih | bs_capply _ _ ih | bs_unwrap _ _ ih
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih =>
    intro hc hnt; exact ih hc hnt
  | bs_letin_val hbs1 hv hwf hfresh hbs2 ih1 ih2 =>
    intro hc hnt
    rw [Trace.touched_append, not_or] at hnt
    have h1 := ih1 hc hnt.1
    have hc1 : _ ≠ none := h1 ▸ hc
    have hne : c ≠ _ := fun h => hc1 (h ▸ hfresh)
    have h2 := ih2 (by rw [Memory.extend_val_lookup_ne hne]; exact hc1) hnt.2
    rw [h2, Memory.extend_val_lookup_ne hne, h1]
  | bs_letin_var hbs1 hbs2 ih1 ih2 | bs_unpack hbs1 hbs2 ih1 ih2 =>
    intro hc hnt
    rw [Trace.touched_append, not_or] at hnt
    have h1 := ih1 hc hnt.1
    have h2 := ih2 (h1 ▸ hc) hnt.2
    rw [h2, h1]
  | bs_par hbs1 hbs2 ih1 ih2 =>
    intro hc hnt
    rw [Trace.touched_append, not_or] at hnt
    have h1 := ih1 hc hnt.1
    have h2 := ih2 (h1 ▸ hc) hnt.2
    rw [h2, h1]

/-- `reachability_of_loc` is insensitive to the mcell bits/liveness of a single
  capability cell `c`: two heaps that agree off `c` and both hold *a* capability
  at `c` agree on `reachability_of_loc` everywhere (a capability always reaches
  `singleton .epsilon c`, irrespective of its bit). -/
theorem reachability_of_loc_frame {h1 h2 : Heap} {c : Nat} {ci1 ci2}
    (hc1 : h1 c = some (.capability ci1)) (hc2 : h2 c = some (.capability ci2))
    (hag : ∀ l, l ≠ c → h1 l = h2 l) (l : Nat) :
    reachability_of_loc h1 l = reachability_of_loc h2 l := by
  by_cases hlc : l = c
  · subst hlc; simp only [reachability_of_loc, hc1, hc2]
  · simp only [reachability_of_loc, hag l hlc]

/-- `expand_captures` is determined by `reachability_of_loc`, so it agrees between
  heaps with matching `reachability_of_loc`. -/
theorem expand_captures_frame {h1 h2 : Heap} (cs : CaptureSet {})
    (hr : ∀ l, reachability_of_loc h1 l = reachability_of_loc h2 l) :
    expand_captures h1 cs = expand_captures h2 cs := by
  induction cs with
  | empty => rfl
  | var m x => cases x with
    | bound bv => cases bv
    | free loc => simp only [expand_captures, hr loc]
  | cvar m C => cases C
  | union cs1 cs2 ih1 ih2 => simp only [expand_captures, ih1, ih2]

/-- `compute_reachability` frame: two heaps that agree off a single capability cell
  `c` (both holding a capability at `c`) compute the same reachability for any
  simple value. -/
theorem compute_reachability_frame {h1 h2 : Heap} {c : Nat} {ci1 ci2}
    (hc1 : h1 c = some (.capability ci1)) (hc2 : h2 c = some (.capability ci2))
    (hag : ∀ l, l ≠ c → h1 l = h2 l) (v : Exp {}) (hv : v.IsSimpleVal) :
    compute_reachability h1 v hv = compute_reachability h2 v hv := by
  have hr := reachability_of_loc_frame hc1 hc2 hag
  cases hv with
  | abs | tabs | cabs | boxed =>
    exact expand_captures_frame _ hr
  | reader => rename_i x; cases x with | free loc => rfl | bound bx => cases bx
  | unit | btrue | bfalse => rfl

/-- **Exact memory frame.**  If `e` runs from `ma`, and `mb` agrees with `ma` on
  every cell except `c` (a capability cell of `ma` that `e` never touches), then
  `e` replays from `mb` with the SAME trace and value, the results agree off `c`,
  and `c` is unchanged in the `mb`-run.  This is the bit-exact strengthening of
  `simulate_down` (whose `subsumes` discards mcell bits) needed for the par diamond. -/
theorem BigStep.frame_off {ma mb : Memory} {e : Exp {}} {t v ma' : _} {c : Nat}
    (hbs : BigStep ma e t v ma')
    (hc : ∃ ci, ma.lookup c = some (.capability ci))
    (hcb : ∃ ci, mb.lookup c = some (.capability ci))
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hnt : ¬ Trace.touched t c)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', BigStep mb e t v mb' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = mb.lookup c := by
  induction hbs generalizing mb with
  | bs_pack =>
    exact ⟨mb, BigStep.bs_pack, hag, rfl⟩
  | bs_val hv =>
    exact ⟨mb, BigStep.bs_val hv, hag, rfl⟩
  | bs_var =>
    exact ⟨mb, BigStep.bs_var, hag, rfl⟩
  | bs_wrap =>
    exact ⟨mb, BigStep.bs_wrap, hag, rfl⟩
  | bs_alloc hlk hfresh =>
    obtain ⟨ci, hci⟩ := hc
    rename_i ll
    have hlc : ll ≠ c := fun h => by subst h; rw [Memory.lookup, hfresh] at hci; cases hci
    match hwf with
    | .wf_alloc (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by rw [h] at hlk; rw [hci] at hlk; cases hlk
      have hlkb := (hag xx hxc) ▸ hlk
      have hfreshb : mb.heap ll = none := by
        rw [show mb.heap ll = _ from (hag ll hlc).symm]; exact hfresh
      refine ⟨mb.extend_mcell ll _ hfreshb, BigStep.bs_alloc hlkb hfreshb, ?_, ?_⟩
      · intro l hlc'
        by_cases hll : l = ll
        · subst hll
          rw [Memory.extend_mcell_lookup hfresh, Memory.extend_mcell_lookup hfreshb]
        · simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hll]
          exact hag l hlc'
      · have hcl : c ≠ ll := fun h => hlc h.symm
        simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hcl]
  | bs_invoke hlkx hlky =>
    obtain ⟨ci, hci⟩ := hc
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) (.wf_free (n := yy) hy1) =>
      have hxc : xx ≠ c := fun h => hnt (Or.inl h.symm)
      have hyc : yy ≠ c := fun h => by rw [h] at hlky; rw [hci] at hlky; cases hlky
      exact ⟨mb, BigStep.bs_invoke ((hag xx hxc) ▸ hlkx) ((hag yy hyc) ▸ hlky), hag, rfl⟩
  | bs_apply hlk hbody ih =>
    obtain ⟨ci, hci⟩ := hc
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) hwfy =>
      have hxc : xx ≠ c := fun h => by rw [h] at hlk; rw [hci] at hlk; cases hlk
      have hlkb := (hag xx hxc) ▸ hlk
      obtain ⟨_, _, he⟩ := Exp.wf_inv_abs (Memory.wf_lookup hlkb)
      obtain ⟨mb', hbsb, hag', hcpres⟩ :=
        ih ⟨ci, hci⟩ hcb hag hnt (Exp.wf_subst he (Subst.wf_openVar hwfy))
      exact ⟨mb', BigStep.bs_apply hlkb hbsb, hag', hcpres⟩
  | bs_tapply hlk hbody ih =>
    obtain ⟨ci, hci⟩ := hc
    match hwf with
    | .wf_tapp (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := fun h => by rw [h] at hlk; rw [hci] at hlk; cases hlk
      have hlkb := (hag xx hxc) ▸ hlk
      obtain ⟨_, _, he⟩ := Exp.wf_inv_tabs (Memory.wf_lookup hlkb)
      obtain ⟨mb', hbsb, hag', hcpres⟩ :=
        ih ⟨ci, hci⟩ hcb hag hnt (Exp.wf_subst he (Subst.wf_openTVar Ty.WfInHeap.wf_top))
      exact ⟨mb', BigStep.bs_tapply hlkb hbsb, hag', hcpres⟩
  | bs_capply hlk hbody ih =>
    obtain ⟨ci, hci⟩ := hc
    match hwf with
    | .wf_capp (.wf_free (n := xx) hx1) hcs =>
      have hxc : xx ≠ c := fun h => by rw [h] at hlk; rw [hci] at hlk; cases hlk
      have hlkb := (hag xx hxc) ▸ hlk
      obtain ⟨_, _, he⟩ := Exp.wf_inv_cabs (Memory.wf_lookup hlkb)
      obtain ⟨mb', hbsb, hag', hcpres⟩ :=
        ih ⟨ci, hci⟩ hcb hag hnt (Exp.wf_subst he (Subst.wf_openCVar hcs))
      exact ⟨mb', BigStep.bs_capply hlkb hbsb, hag', hcpres⟩
  | bs_unwrap hlk hbody ih =>
    obtain ⟨ci, hci⟩ := hc
    match hwf with
    | .wf_unwrap (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by rw [h] at hlk; rw [hci] at hlk; cases hlk
      have hlkb := (hag xx hxc) ▸ hlk
      obtain ⟨mb', hbsb, hag', hcpres⟩ :=
        ih ⟨ci, hci⟩ hcb hag hnt (match Memory.wf_lookup hlkb with | .wf_boxed _ _ he => he)
      exact ⟨mb', BigStep.bs_unwrap hlkb hbsb, hag', hcpres⟩
  | bs_read hlkx hlky =>
    obtain ⟨ci, hci⟩ := hc
    match hwf with
    | .wf_read (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by rw [h] at hlkx; rw [hci] at hlkx; cases hlkx
      have hyc : _ ≠ c := fun h => hnt (Or.inl h.symm)
      exact ⟨mb, BigStep.bs_read ((hag xx hxc) ▸ hlkx) ((hag _ hyc) ▸ hlky), hag, rfl⟩
  | bs_write_true hlkx hlky =>
    obtain ⟨ci, hci⟩ := hc
    rename_i x y _ _ _
    have hxc : x ≠ c := fun h => hnt (Or.inl h.symm)
    have hyc : y ≠ c := fun h => by rw [h] at hlky; rw [hci] at hlky; cases hlky
    have hlkxb := (hag x hxc) ▸ hlkx
    refine ⟨mb.update_mcell x true .live ⟨_, hlkxb⟩,
      BigStep.bs_write_true hlkxb ((hag y hyc) ▸ hlky), ?_, ?_⟩
    · intro l hlc
      by_cases hlx : l = x
      · subst hlx
        simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
      · rw [Memory.update_mcell_lookup_ne hlx, Memory.update_mcell_lookup_ne hlx]; exact hag l hlc
    · exact Memory.update_mcell_lookup_ne (fun h => hxc h.symm)
  | bs_write_false hlkx hlky =>
    obtain ⟨ci, hci⟩ := hc
    rename_i x y _ _ _
    have hxc : x ≠ c := fun h => hnt (Or.inl h.symm)
    have hyc : y ≠ c := fun h => by rw [h] at hlky; rw [hci] at hlky; cases hlky
    have hlkxb := (hag x hxc) ▸ hlkx
    refine ⟨mb.update_mcell x false .live ⟨_, hlkxb⟩,
      BigStep.bs_write_false hlkxb ((hag y hyc) ▸ hlky), ?_, ?_⟩
    · intro l hlc
      by_cases hlx : l = x
      · subst hlx
        simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
      · rw [Memory.update_mcell_lookup_ne hlx, Memory.update_mcell_lookup_ne hlx]; exact hag l hlc
    · exact Memory.update_mcell_lookup_ne (fun h => hxc h.symm)
  | bs_drop hlkx =>
    obtain ⟨ci, hci⟩ := hc
    rename_i x _
    have hxc : x ≠ c := fun h => hnt (Or.inl h.symm)
    have hlkxb := (hag x hxc) ▸ hlkx
    refine ⟨mb.drop_mcell x ⟨_, hlkxb⟩, BigStep.bs_drop hlkxb, ?_, ?_⟩
    · intro l hlc
      by_cases hlx : l = x
      · subst hlx
        simp only [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_true]
      · rw [Memory.drop_mcell_lookup_ne hlx, Memory.drop_mcell_lookup_ne hlx]; exact hag l hlc
    · exact Memory.drop_mcell_lookup_ne (fun h => hxc h.symm)
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    obtain ⟨ci, hci⟩ := hc
    obtain ⟨cib, hcib⟩ := hcb
    rename_i vval l'
    rw [Trace.touched_append, not_or] at hnt
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    obtain ⟨mb1, run1, ag1, cpres1⟩ := ih1 ⟨ci, hci⟩ ⟨cib, hcib⟩ hag hnt.1 hwf_e1
    have hc_m1 := (BigStep.untouched_preserved hbs1 (by rw [hci]; simp) hnt.1).trans hci
    have hc_mb1 := cpres1.trans hcib
    have hl'c : l' ≠ c := fun h => by rw [h, hc_m1] at hfresh; cases hfresh
    have hfreshb : mb1.lookup l' = none := (ag1 l' hl'c).symm.trans hfresh
    have hwf_vb := BigStep.wf_answer run1 hwf_e1
    have hreach_eq := compute_reachability_frame hc_m1 hc_mb1 ag1 vval hv
    obtain ⟨mb2, run2, ag2, cpres2⟩ :=
      ih2 (mb := mb1.extend_val l' ⟨vval, hv, compute_reachability mb1.heap vval hv⟩
              hwf_vb rfl hfreshb)
        ⟨ci, by rw [Memory.extend_val_lookup_ne (Ne.symm hl'c)]; exact hc_m1⟩
        ⟨cib, by rw [Memory.extend_val_lookup_ne (Ne.symm hl'c)]; exact hc_mb1⟩
        (by
          intro l hlc
          by_cases hll : l = l'
          · subst hll
            rw [Memory.extend_val_lookup_self, Memory.extend_val_lookup_self]
            exact congrArg (fun R => some (Cell.val ⟨vval, hv, R⟩)) hreach_eq
          · rw [Memory.extend_val_lookup_ne hll, Memory.extend_val_lookup_ne hll]
            exact ag1 l hlc)
        hnt.2
        (Exp.wf_subst
          (Exp.wf_monotonic
            (Heap.subsumes_trans (Heap.extend_subsumes hfreshb) (BigStep.subsumes run1))
            hwf_e2)
          (Subst.wf_openVar (Var.WfInHeap.wf_free (Heap.extend_lookup_eq _ _ _))))
    refine ⟨mb2, BigStep.bs_letin_val run1 hv hwf_vb hfreshb run2, ag2, ?_⟩
    rw [cpres2, Memory.extend_val_lookup_ne (Ne.symm hl'c)]; exact cpres1
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    obtain ⟨ci, hci⟩ := hc
    obtain ⟨cib, hcib⟩ := hcb
    rw [Trace.touched_append, not_or] at hnt
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    obtain ⟨mb1, run1, ag1, cpres1⟩ := ih1 ⟨ci, hci⟩ ⟨cib, hcib⟩ hag hnt.1 hwf_e1
    have hc1 := BigStep.untouched_preserved hbs1 (by rw [hci]; simp) hnt.1
    have hwf_body := Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes run1) hwf_e2)
      (match BigStep.wf_answer run1 hwf_e1 with
        | Exp.WfInHeap.wf_var hx => Subst.wf_openVar hx)
    obtain ⟨mb2, run2, ag2, cpres2⟩ :=
      ih2 ⟨ci, hc1.trans hci⟩ ⟨cib, cpres1.trans hcib⟩ ag1 hnt.2 hwf_body
    exact ⟨mb2, BigStep.bs_letin_var run1 run2, ag2, cpres2.trans cpres1⟩
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    obtain ⟨ci, hci⟩ := hc
    obtain ⟨cib, hcib⟩ := hcb
    rw [Trace.touched_append, not_or] at hnt
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_unpack hwf
    obtain ⟨mb1, run1, ag1, cpres1⟩ := ih1 ⟨ci, hci⟩ ⟨cib, hcib⟩ hag hnt.1 hwf_e1
    have hc1 := BigStep.untouched_preserved hbs1 (by rw [hci]; simp) hnt.1
    have hwf_body := Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes run1) hwf_e2)
      (match BigStep.wf_answer run1 hwf_e1 with
        | Exp.WfInHeap.wf_pack hcs hx => Subst.wf_unpack hcs hx)
    obtain ⟨mb2, run2, ag2, cpres2⟩ :=
      ih2 ⟨ci, hc1.trans hci⟩ ⟨cib, cpres1.trans hcib⟩ ag1 hnt.2 hwf_body
    exact ⟨mb2, BigStep.bs_unpack run1 run2, ag2, cpres2.trans cpres1⟩
  | bs_cond_true hres hbody ih =>
    obtain ⟨ci, hci⟩ := hc
    rw [Memory.lookup] at hci
    obtain ⟨hwfx, hwf2, _⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := fun h => by simp only [resolve, h, hci] at hres; cases hres
      have hresb : resolve mb.heap (.var (.free xb)) = some .btrue := by
        simp only [resolve] at hres ⊢
        rw [show mb.heap xb = _ from (hag xb hxc).symm]; exact hres
      obtain ⟨mb', hbsb, hag', hcpres⟩ := ih ⟨ci, by rw [Memory.lookup]; exact hci⟩ hcb hag hnt hwf2
      exact ⟨mb', BigStep.bs_cond_true hresb hbsb, hag', hcpres⟩
  | bs_cond_false hres hbody ih =>
    obtain ⟨ci, hci⟩ := hc
    rw [Memory.lookup] at hci
    obtain ⟨hwfx, _, hwf3⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := fun h => by simp only [resolve, h, hci] at hres; cases hres
      have hresb : resolve mb.heap (.var (.free xb)) = some .bfalse := by
        simp only [resolve] at hres ⊢
        rw [show mb.heap xb = _ from (hag xb hxc).symm]; exact hres
      obtain ⟨mb', hbsb, hag', hcpres⟩ := ih ⟨ci, by rw [Memory.lookup]; exact hci⟩ hcb hag hnt hwf3
      exact ⟨mb', BigStep.bs_cond_false hresb hbsb, hag', hcpres⟩
  | bs_par hbs1 hbs2 ih1 ih2 =>
    obtain ⟨ci, hci⟩ := hc
    obtain ⟨cib, hcib⟩ := hcb
    rw [Trace.touched_append, not_or] at hnt
    match hwf with
    | .wf_par _ _ hwf_e1 hwf_e2 =>
      obtain ⟨mb1, run1, ag1, cpres1⟩ := ih1 ⟨ci, hci⟩ ⟨cib, hcib⟩ hag hnt.1 hwf_e1
      have hc1 := BigStep.untouched_preserved hbs1 (by rw [hci]; simp) hnt.1
      obtain ⟨mb2, run2, ag2, cpres2⟩ :=
        ih2 ⟨ci, hc1.trans hci⟩ ⟨cib, cpres1.trans hcib⟩ ag1 hnt.2
          (Exp.wf_monotonic (BigStep.subsumes run1) hwf_e2)
      exact ⟨mb2, BigStep.bs_par run1 run2, ag2, cpres2.trans cpres1⟩

/-- `expand_captures` frame indexed by well-formedness: a capture set that is
  `WfInHeap h2` pins each of its free locations into `h2`'s domain.  When `h2`
  agrees with `h1` off a cell `c` that is *absent* in `h2`, every such location
  differs from `c`, so the two heaps agree there and `expand_captures` matches. -/
theorem expand_captures_frame_wf {h1 h2 : Heap} {c : Nat} (cs : CaptureSet {})
    (hwf : CaptureSet.WfInHeap cs h2) (hc2 : h2 c = none)
    (hag : ∀ l, l ≠ c → h1 l = h2 l) :
    expand_captures h1 cs = expand_captures h2 cs := by
  induction hwf with
  | wf_empty => rfl
  | wf_union _ _ ih1 ih2 => simp only [expand_captures, ih1 hc2 hag, ih2 hc2 hag]
  | wf_var_free hex =>
    rename_i _ loc
    have hlc : loc ≠ c := fun h => by rw [h, hc2] at hex; cases hex
    simp only [expand_captures, reachability_of_loc, hag loc hlc]
  | @wf_var_bound _ x _ => cases x
  | @wf_cvar _ x _ => cases x

/-- `compute_reachability` frame for an absent cell: a simple value that is
  `WfInHeap h2` (with `c` absent in `h2`, so it cannot reference `c`) computes the
  same reachability in `h1` as in `h2`, whenever the heaps agree off `c`. -/
theorem compute_reachability_frame_wf {h1 h2 : Heap} {c : Nat}
    (hc2 : h2 c = none) (hag : ∀ l, l ≠ c → h1 l = h2 l)
    (v : Exp {}) (hv : v.IsSimpleVal) (hwf : Exp.WfInHeap v h2) :
    compute_reachability h1 v hv = compute_reachability h2 v hv := by
  cases hv with
  | abs => cases hwf with | wf_abs hcs _ _ => exact expand_captures_frame_wf _ hcs hc2 hag
  | tabs => cases hwf with | wf_tabs hcs _ _ => exact expand_captures_frame_wf _ hcs hc2 hag
  | cabs => cases hwf with | wf_cabs hcs _ _ => exact expand_captures_frame_wf _ hcs hc2 hag
  | boxed => cases hwf with | wf_boxed hcs _ _ => exact expand_captures_frame_wf _ hcs hc2 hag
  | reader => rename_i x; cases x with | free loc => rfl | bound bx => cases bx
  | unit | btrue | bfalse => rfl

/-- Exact memory frame, absent variant: `c` is PRESENT in `ma` but ABSENT in `mb`.
  Since `e` is well-formed in `mb`, it cannot reference `c` (a `none` location), so
  it neither touches nor captures `c`; thus it replays from `mb`, the results agree
  off `c`, and `c` stays `none`.  The disequalities `loc ≠ c` come from `mb`-side
  well-formedness (`mb`'s domain excludes `c`) rather than from `c`'s cell kind, so
  this works for `c` of ANY kind in `ma` (capability OR value). -/
theorem BigStep.frame_off_absent {ma mb : Memory} {e : Exp {}} {t v ma' : _} {c : Nat}
    (hbs : BigStep ma e t v ma')
    (hc : ma.lookup c ≠ none)
    (hcb : mb.lookup c = none)
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', BigStep mb e t v mb' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = none ∧ ¬ Trace.touched t c := by
  induction hbs generalizing mb with
  | bs_pack =>
    exact ⟨mb, BigStep.bs_pack, hag, hcb, by simp [Trace.touched]⟩
  | bs_val hv =>
    exact ⟨mb, BigStep.bs_val hv, hag, hcb, by simp [Trace.touched]⟩
  | bs_var =>
    exact ⟨mb, BigStep.bs_var, hag, hcb, by simp [Trace.touched]⟩
  | bs_wrap =>
    exact ⟨mb, BigStep.bs_wrap, hag, hcb, by simp [Trace.touched]⟩
  | bs_alloc hlk hfresh =>
    rename_i ll
    have hlc : ll ≠ c := fun h => by rw [h] at hfresh; exact hc hfresh
    match hwf with
    | .wf_alloc (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hlkb := (hag xx hxc) ▸ hlk
      have hfreshb : mb.heap ll = none := by
        rw [show mb.heap ll = _ from (hag ll hlc).symm]; exact hfresh
      refine ⟨mb.extend_mcell ll _ hfreshb, BigStep.bs_alloc hlkb hfreshb, ?_, ?_,
        by simp [Trace.touched]⟩
      · intro l hlc'
        by_cases hll : l = ll
        · subst hll
          rw [Memory.extend_mcell_lookup hfresh, Memory.extend_mcell_lookup hfreshb]
        · simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hll]
          exact hag l hlc'
      · have hcl : c ≠ ll := fun h => hlc h.symm
        simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hcl]
        exact hcb
  | bs_invoke hlkx hlky =>
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) (.wf_free (n := yy) hy1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hyc : yy ≠ c := fun h => by
        rw [h] at hy1; rw [show mb.heap c = none from hcb] at hy1; cases hy1
      exact ⟨mb, BigStep.bs_invoke ((hag xx hxc) ▸ hlkx) ((hag yy hyc) ▸ hlky), hag, hcb,
        by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
  | bs_apply hlk hbody ih =>
    match hwf with
    | .wf_app (.wf_free (n := xx) hx1) hwfy =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hlkb := (hag xx hxc) ▸ hlk
      obtain ⟨_, _, he⟩ := Exp.wf_inv_abs (Memory.wf_lookup hlkb)
      obtain ⟨mb', hbsb, hag', hcpres, hnt'⟩ :=
        ih hc hcb hag (Exp.wf_subst he (Subst.wf_openVar hwfy))
      exact ⟨mb', BigStep.bs_apply hlkb hbsb, hag', hcpres, hnt'⟩
  | bs_tapply hlk hbody ih =>
    match hwf with
    | .wf_tapp (.wf_free (n := xx) hx1) _ =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hlkb := (hag xx hxc) ▸ hlk
      obtain ⟨_, _, he⟩ := Exp.wf_inv_tabs (Memory.wf_lookup hlkb)
      obtain ⟨mb', hbsb, hag', hcpres, hnt'⟩ :=
        ih hc hcb hag (Exp.wf_subst he (Subst.wf_openTVar Ty.WfInHeap.wf_top))
      exact ⟨mb', BigStep.bs_tapply hlkb hbsb, hag', hcpres, hnt'⟩
  | bs_capply hlk hbody ih =>
    match hwf with
    | .wf_capp (.wf_free (n := xx) hx1) hcs =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hlkb := (hag xx hxc) ▸ hlk
      obtain ⟨_, _, he⟩ := Exp.wf_inv_cabs (Memory.wf_lookup hlkb)
      obtain ⟨mb', hbsb, hag', hcpres, hnt'⟩ :=
        ih hc hcb hag (Exp.wf_subst he (Subst.wf_openCVar hcs))
      exact ⟨mb', BigStep.bs_capply hlkb hbsb, hag', hcpres, hnt'⟩
  | bs_unwrap hlk hbody ih =>
    match hwf with
    | .wf_unwrap (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hlkb := (hag xx hxc) ▸ hlk
      obtain ⟨mb', hbsb, hag', hcpres, hnt'⟩ :=
        ih hc hcb hag (match Memory.wf_lookup hlkb with | .wf_boxed _ _ he => he)
      exact ⟨mb', BigStep.bs_unwrap hlkb hbsb, hag', hcpres, hnt'⟩
  | bs_read hlkx hlky =>
    match hwf with
    | .wf_read (.wf_free (n := xx) hx1) =>
      have hxc : xx ≠ c := fun h => by
        rw [h] at hx1; rw [show mb.heap c = none from hcb] at hx1; cases hx1
      have hlkxb := (hag xx hxc) ▸ hlkx
      match Memory.wf_lookup hlkxb with
      | .wf_reader (.wf_free (n := yy) hy1) =>
        have hyc : yy ≠ c := fun h => by
          rw [h] at hy1; rw [show mb.heap c = none from hcb] at hy1; cases hy1
        exact ⟨mb, BigStep.bs_read hlkxb ((hag yy hyc) ▸ hlky), hag, hcb,
          by simp only [Trace.touched, or_false]; exact fun h => hyc h.symm⟩
  | bs_write_true hlkx hlky =>
    rename_i x y _ _ _
    have hxx : mb.heap x ≠ none := by
      cases hwf with | wf_write hwfx _ => cases hwfx with | wf_free h => rw [h]; simp
    have hyx : mb.heap y ≠ none := by
      cases hwf with | wf_write _ hwfy => cases hwfy with | wf_free h => rw [h]; simp
    have hxc : x ≠ c := fun h => hxx (by rw [h]; exact hcb)
    have hyc : y ≠ c := fun h => hyx (by rw [h]; exact hcb)
    have hlkxb := (hag x hxc) ▸ hlkx
    refine ⟨mb.update_mcell x true .live ⟨_, hlkxb⟩,
      BigStep.bs_write_true hlkxb ((hag y hyc) ▸ hlky), ?_, ?_,
      by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
    · intro l hlc
      by_cases hlx : l = x
      · subst hlx
        simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
      · rw [Memory.update_mcell_lookup_ne hlx, Memory.update_mcell_lookup_ne hlx]
        exact hag l hlc
    · rw [Memory.update_mcell_lookup_ne (fun h => hxc h.symm)]; exact hcb
  | bs_write_false hlkx hlky =>
    rename_i x y _ _ _
    have hxx : mb.heap x ≠ none := by
      cases hwf with | wf_write hwfx _ => cases hwfx with | wf_free h => rw [h]; simp
    have hyx : mb.heap y ≠ none := by
      cases hwf with | wf_write _ hwfy => cases hwfy with | wf_free h => rw [h]; simp
    have hxc : x ≠ c := fun h => hxx (by rw [h]; exact hcb)
    have hyc : y ≠ c := fun h => hyx (by rw [h]; exact hcb)
    have hlkxb := (hag x hxc) ▸ hlkx
    refine ⟨mb.update_mcell x false .live ⟨_, hlkxb⟩,
      BigStep.bs_write_false hlkxb ((hag y hyc) ▸ hlky), ?_, ?_,
      by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
    · intro l hlc
      by_cases hlx : l = x
      · subst hlx
        simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
      · rw [Memory.update_mcell_lookup_ne hlx, Memory.update_mcell_lookup_ne hlx]
        exact hag l hlc
    · rw [Memory.update_mcell_lookup_ne (fun h => hxc h.symm)]; exact hcb
  | bs_drop hlkx =>
    rename_i xx _
    have hxx : mb.heap xx ≠ none := by
      cases hwf with | wf_drop hwfx => cases hwfx with | wf_free h => rw [h]; simp
    have hxc : xx ≠ c := fun h => hxx (by rw [h]; exact hcb)
    have hlkxb := (hag xx hxc) ▸ hlkx
    refine ⟨mb.drop_mcell xx ⟨_, hlkxb⟩, BigStep.bs_drop hlkxb, ?_, ?_,
      by simp only [Trace.touched, or_false]; exact fun h => hxc h.symm⟩
    · intro l hlc
      by_cases hlx : l = xx
      · subst hlx
        simp only [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_true]
      · rw [Memory.drop_mcell_lookup_ne hlx, Memory.drop_mcell_lookup_ne hlx]; exact hag l hlc
    · rw [Memory.drop_mcell_lookup_ne (fun h => hxc h.symm)]; exact hcb
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    rename_i vval l'
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    obtain ⟨mb1, run1, ag1, cpres1, hnt1⟩ := ih1 hc hcb hag hwf_e1
    have hc_m1 : _ ≠ none :=
      fun h => hc ((BigStep.untouched_preserved hbs1 hc hnt1).symm.trans h)
    have hl'c : l' ≠ c := fun h => by subst h; exact hc_m1 hfresh
    have hfreshb : mb1.lookup l' = none := (ag1 l' hl'c).symm.trans hfresh
    have hwf_vb := BigStep.wf_answer run1 hwf_e1
    have hreach_eq := compute_reachability_frame_wf cpres1 ag1 vval hv hwf_vb
    obtain ⟨mb2, run2, ag2, cpres2, hnt2⟩ :=
      ih2 (mb := mb1.extend_val l' ⟨vval, hv, compute_reachability mb1.heap vval hv⟩
              hwf_vb rfl hfreshb)
        (by rw [Memory.extend_val_lookup_ne (Ne.symm hl'c)]; exact hc_m1)
        (by rw [Memory.extend_val_lookup_ne (Ne.symm hl'c)]; exact cpres1)
        (by
          intro l hlc
          by_cases hll : l = l'
          · subst hll
            rw [Memory.extend_val_lookup_self, Memory.extend_val_lookup_self]
            exact congrArg (fun R => some (Cell.val ⟨vval, hv, R⟩)) hreach_eq
          · rw [Memory.extend_val_lookup_ne hll, Memory.extend_val_lookup_ne hll]
            exact ag1 l hlc)
        (Exp.wf_subst
          (Exp.wf_monotonic
            (Heap.subsumes_trans (Heap.extend_subsumes hfreshb) (BigStep.subsumes run1))
            hwf_e2)
          (Subst.wf_openVar (Var.WfInHeap.wf_free (Heap.extend_lookup_eq _ _ _))))
    exact ⟨mb2, BigStep.bs_letin_val run1 hv hwf_vb hfreshb run2, ag2, cpres2,
      by rw [Trace.touched_append, not_or]; exact ⟨hnt1, hnt2⟩⟩
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    obtain ⟨mb1, run1, ag1, cpres1, hnt1⟩ := ih1 hc hcb hag hwf_e1
    have hc1 : _ ≠ none :=
      fun h => hc ((BigStep.untouched_preserved hbs1 hc hnt1).symm.trans h)
    have hwf_body := Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes run1) hwf_e2)
      (match BigStep.wf_answer run1 hwf_e1 with
        | Exp.WfInHeap.wf_var hx => Subst.wf_openVar hx)
    obtain ⟨mb2, run2, ag2, cpres2, hnt2⟩ := ih2 hc1 cpres1 ag1 hwf_body
    exact ⟨mb2, BigStep.bs_letin_var run1 run2, ag2, cpres2,
      by rw [Trace.touched_append, not_or]; exact ⟨hnt1, hnt2⟩⟩
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_unpack hwf
    obtain ⟨mb1, run1, ag1, cpres1, hnt1⟩ := ih1 hc hcb hag hwf_e1
    have hc1 : _ ≠ none :=
      fun h => hc ((BigStep.untouched_preserved hbs1 hc hnt1).symm.trans h)
    have hwf_body := Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes run1) hwf_e2)
      (match BigStep.wf_answer run1 hwf_e1 with
        | Exp.WfInHeap.wf_pack hcs hx => Subst.wf_unpack hcs hx)
    obtain ⟨mb2, run2, ag2, cpres2, hnt2⟩ := ih2 hc1 cpres1 ag1 hwf_body
    exact ⟨mb2, BigStep.bs_unpack run1 run2, ag2, cpres2,
      by rw [Trace.touched_append, not_or]; exact ⟨hnt1, hnt2⟩⟩
  | bs_cond_true hres hbody ih =>
    obtain ⟨hwfx, hwf2, _⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := fun h => by
        rw [h] at hxb; rw [show mb.heap c = none from hcb] at hxb; cases hxb
      have hresb : resolve mb.heap (.var (.free xb)) = some .btrue := by
        simp only [resolve] at hres ⊢
        rw [show mb.heap xb = _ from (hag xb hxc).symm]; exact hres
      obtain ⟨mb', hbsb, hag', hcpres, hnt'⟩ := ih hc hcb hag hwf2
      exact ⟨mb', BigStep.bs_cond_true hresb hbsb, hag', hcpres, hnt'⟩
  | bs_cond_false hres hbody ih =>
    obtain ⟨hwfx, _, hwf3⟩ := Exp.wf_inv_cond hwf
    match hwfx with
    | .wf_free (n := xb) hxb =>
      have hxc : xb ≠ c := fun h => by
        rw [h] at hxb; rw [show mb.heap c = none from hcb] at hxb; cases hxb
      have hresb : resolve mb.heap (.var (.free xb)) = some .bfalse := by
        simp only [resolve] at hres ⊢
        rw [show mb.heap xb = _ from (hag xb hxc).symm]; exact hres
      obtain ⟨mb', hbsb, hag', hcpres, hnt'⟩ := ih hc hcb hag hwf3
      exact ⟨mb', BigStep.bs_cond_false hresb hbsb, hag', hcpres, hnt'⟩
  | bs_par hbs1 hbs2 ih1 ih2 =>
    match hwf with
    | .wf_par _ _ hwf_e1 hwf_e2 =>
      obtain ⟨mb1, run1, ag1, cpres1, hnt1⟩ := ih1 hc hcb hag hwf_e1
      have hc1 : _ ≠ none :=
        fun h => hc ((BigStep.untouched_preserved hbs1 hc hnt1).symm.trans h)
      obtain ⟨mb2, run2, ag2, cpres2, hnt2⟩ :=
        ih2 hc1 cpres1 ag1 (Exp.wf_monotonic (BigStep.subsumes run1) hwf_e2)
      exact ⟨mb2, BigStep.bs_par run1 run2, ag2, cpres2,
        by rw [Trace.touched_append, not_or]; exact ⟨hnt1, hnt2⟩⟩

/-- Exact memory frame, fresh variant: `c` is a capability of `ma` but ABSENT in
  `mb` (the other thread allocated it).  A corollary of `frame_off_absent`. -/
theorem BigStep.frame_off_fresh {ma mb : Memory} {e : Exp {}} {t v ma' : _} {c : Nat}
    (hbs : BigStep ma e t v ma')
    (hc : ∃ ci, ma.lookup c = some (.capability ci))
    (hcb : mb.lookup c = none)
    (hag : ∀ l, l ≠ c → ma.lookup l = mb.lookup l)
    (hwf : Exp.WfInHeap e mb.heap) :
    ∃ mb', BigStep mb e t v mb' ∧ (∀ l, l ≠ c → ma'.lookup l = mb'.lookup l) ∧
      mb'.lookup c = none ∧ ¬ Trace.touched t c :=
  BigStep.frame_off_absent hbs (by obtain ⟨ci, h⟩ := hc; rw [h]; simp) hcb hag hwf

/-- Two memories with equal heaps are equal (the `wf`/`findom` fields are `Prop`s,
  so proof-irrelevant once the heap is fixed). -/
theorem Memory.ext {m1 m2 : Memory} (h : m1.heap = m2.heap) : m1 = m2 := by
  cases m1; cases m2; cases h; rfl

/-- Two memories agreeing on every lookup are equal. -/
theorem Memory.ext_lookup {m1 m2 : Memory} (h : ∀ l, m1.lookup l = m2.lookup l) : m1 = m2 :=
  Memory.ext (funext h)

/-- **Value cells are immutable across a run.**  A `.val` cell present in the
  starting memory is preserved verbatim by any `BigStep`: writes/drops only target
  capability mcells, and `alloc`/`extend` only target fresh locations. -/
theorem BigStep.val_preserved {m : Memory} {e : Exp {}} {t v m' : _} {l : Nat} {w}
    (hbs : BigStep m e t v m') (hl : m.lookup l = some (.val w)) :
    m'.lookup l = some (.val w) := by
  induction hbs with
  | bs_pack | bs_val _ | bs_var | bs_wrap | bs_invoke _ _ | bs_read _ _ => exact hl
  | bs_alloc _ hfresh =>
    have hne : l ≠ _ := fun h => by rw [h, Memory.lookup, hfresh] at hl; cases hl
    simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hne]
    exact hl
  | bs_write_true hx _ | bs_write_false hx _ =>
    have hne : l ≠ _ := fun h => by rw [h, hx] at hl; cases hl
    rw [Memory.update_mcell_lookup_ne hne]; exact hl
  | bs_drop hx =>
    have hne : l ≠ _ := fun h => by rw [h, hx] at hl; cases hl
    rw [Memory.drop_mcell_lookup_ne hne]; exact hl
  | bs_apply _ _ ih | bs_tapply _ _ ih | bs_capply _ _ ih | bs_unwrap _ _ ih
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih => exact ih hl
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    have h1 := ih1 hl
    have hne : l ≠ _ := fun h => by rw [h] at h1; rw [hfresh] at h1; cases h1
    exact ih2 (by rw [Memory.extend_val_lookup_ne hne]; exact h1)
  | bs_letin_var hbs1 hbs2 ih1 ih2 | bs_unpack hbs1 hbs2 ih1 ih2
  | bs_par hbs1 hbs2 ih1 ih2 => exact ih2 (ih1 hl)

/-- **A run leaves untouched mutable cells unchanged even if it READS them.**  A
  cell `l` (present in `m`) that is neither WRITTEN (`.access .epsilon l`) nor
  DROPPED (`.dealloc l`) by the trace keeps its exact cell — reads (`.access .ro l`)
  are permitted and never mutate.  Stronger than `untouched_preserved`, which forbids
  reads too; this is what pins a read's stored bit across the separated thread. -/
theorem BigStep.unmutated_preserved {m : Memory} {e : Exp {}} {t v m' : _} {l : Nat}
    (hbs : BigStep m e t v m') (hne : m.lookup l ≠ none)
    (hw : ¬ (TraceItem.access .epsilon l ∈ t)) (hd : ¬ (TraceItem.dealloc l ∈ t)) :
    m'.lookup l = m.lookup l := by
  induction hbs with
  | bs_pack | bs_val _ | bs_var | bs_wrap | bs_invoke _ _ | bs_read _ _ => rfl
  | bs_alloc _ hfresh =>
    have hlc : l ≠ _ := fun h => hne (by rw [h]; rw [Memory.lookup]; exact hfresh)
    simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hlc]
  | bs_write_true hx _ | bs_write_false hx _ =>
    have hlc : l ≠ _ := fun h => hw (by rw [h]; exact List.mem_singleton.mpr rfl)
    exact Memory.update_mcell_lookup_ne hlc
  | bs_drop hx =>
    have hlc : l ≠ _ := fun h => hd (by rw [h]; exact List.mem_singleton.mpr rfl)
    exact Memory.drop_mcell_lookup_ne hlc
  | bs_apply _ _ ih | bs_tapply _ _ ih | bs_capply _ _ ih | bs_unwrap _ _ ih
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih => exact ih hne hw hd
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    rw [List.mem_append, not_or] at hw hd
    have h1 := ih1 hne hw.1 hd.1
    have hne1 : _ ≠ none := h1 ▸ hne
    have hlc : l ≠ _ := fun h => hne1 (by rw [h]; exact hfresh)
    have h2 := ih2 (by rw [Memory.extend_val_lookup_ne hlc]; exact hne1) hw.2 hd.2
    rw [h2, Memory.extend_val_lookup_ne hlc, h1]
  | bs_letin_var hbs1 hbs2 ih1 ih2 | bs_unpack hbs1 hbs2 ih1 ih2
  | bs_par hbs1 hbs2 ih1 ih2 =>
    rw [List.mem_append, not_or] at hw hd
    have h1 := ih1 hne hw.1 hd.1
    have h2 := ih2 (h1 ▸ hne) hw.2 hd.2
    rw [h2, h1]

/-- A touched location that the trace does not allocate itself is *externally*
  touched (with some mode).  Generalized over the running allocated set `A`. -/
theorem Trace.extTouchesFromMode_of_touched {t : Trace} {l : Nat} {A : List Nat}
    (hA : l ∉ A) (hal : ¬ Trace.allocd t l) (htc : Trace.touched t l) :
    ∃ cm, Trace.extTouchesFromMode A l cm t := by
  induction t generalizing A with
  | nil => simp only [Trace.touched] at htc
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [Trace.allocd] at hal
      rw [not_or] at hal
      simp only [Trace.touched] at htc
      have hA' : l ∉ l' :: A := by
        simp only [List.mem_cons, not_or]; exact ⟨hal.1, hA⟩
      obtain ⟨cm, hcm⟩ := ih (A := l' :: A) hA' hal.2 htc
      exact ⟨cm, hcm⟩
    | access mu l' =>
      simp only [Trace.allocd] at hal
      simp only [Trace.touched] at htc
      rcases htc with h | h
      · exact ⟨.access mu, Or.inl ⟨h, hA, rfl⟩⟩
      · obtain ⟨cm, hcm⟩ := ih hA hal h
        exact ⟨cm, Or.inr hcm⟩
    | dealloc l' =>
      simp only [Trace.allocd] at hal
      simp only [Trace.touched] at htc
      rcases htc with h | h
      · exact ⟨.drop, Or.inl ⟨h, hA, rfl⟩⟩
      · obtain ⟨cm, hcm⟩ := ih hA hal h
        exact ⟨cm, Or.inr hcm⟩

/-- Top-level corollary: a touched, non-self-allocated location is externally
  touched with some mode. -/
theorem Trace.extTouchesMode_of_touched {t : Trace} {l : Nat}
    (hal : ¬ Trace.allocd t l) (htc : Trace.touched t l) :
    ∃ cm, Trace.extTouchesMode t l cm :=
  Trace.extTouchesFromMode_of_touched (by simp) hal htc

/-- Non-interference + a NON-read-only external touch of `l` by `ts` forbids the
  other trace `s` from touching `l` at all (given `s` does not itself allocate `l`).
  Used to clear write/drop/invoke conflicts in the local diamond. -/
theorem Trace.not_touched_of_noninterfere {s ts : Trace} {l : Nat} {cm : CapMode}
    (hsep : Trace.Noninterfere s ts) (hts : Trace.extTouchesMode ts l cm)
    (hcm : cm ≠ .access .ro) (hnal : ¬ Trace.allocd s l) : ¬ Trace.touched s l := by
  intro htc
  obtain ⟨cm_s, hs⟩ := Trace.extTouchesMode_of_touched hnal htc
  exact hcm (hsep l cm_s cm hs hts).2

/-- A membership of `access mu l` in `t` (with `l` not self-allocated by `t`) yields
  an external touch with mode `.access mu`.  Generalized over the running alloc set. -/
theorem Trace.extTouchesFromMode_of_mem_access {t : Trace} {l : Nat} {mu : Mutability}
    {A : List Nat} (hA : l ∉ A) (hnal : ¬ Trace.allocd t l)
    (hmem : TraceItem.access mu l ∈ t) :
    Trace.extTouchesFromMode A l (.access mu) t := by
  induction t generalizing A with
  | nil => cases hmem
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [Trace.allocd, not_or] at hnal
      have hmem' : TraceItem.access mu l ∈ t := by
        rcases List.mem_cons.mp hmem with h | h
        · cases h
        · exact h
      have hA' : l ∉ l' :: A := by simp only [List.mem_cons, not_or]; exact ⟨hnal.1, hA⟩
      exact ih (A := l' :: A) hA' hnal.2 hmem'
    | access mu' l' =>
      rcases List.mem_cons.mp hmem with h | h
      · have : mu' = mu ∧ l' = l := by cases h; exact ⟨rfl, rfl⟩
        exact Or.inl ⟨this.2.symm, hA, by rw [this.1]⟩
      · simp only [Trace.allocd] at hnal
        exact Or.inr (ih hA hnal h)
    | dealloc l' =>
      have hmem' : TraceItem.access mu l ∈ t := by
        rcases List.mem_cons.mp hmem with h | h
        · cases h
        · exact h
      simp only [Trace.allocd] at hnal
      exact Or.inr (ih hA hnal hmem')

/-- A membership of `dealloc l` in `t` (with `l` not self-allocated) yields an
  external touch with mode `.drop`. -/
theorem Trace.extTouchesFromMode_of_mem_dealloc {t : Trace} {l : Nat}
    {A : List Nat} (hA : l ∉ A) (hnal : ¬ Trace.allocd t l)
    (hmem : TraceItem.dealloc l ∈ t) :
    Trace.extTouchesFromMode A l .drop t := by
  induction t generalizing A with
  | nil => cases hmem
  | cons it t ih =>
    cases it with
    | alloc l' =>
      simp only [Trace.allocd, not_or] at hnal
      have hmem' : TraceItem.dealloc l ∈ t := by
        rcases List.mem_cons.mp hmem with h | h
        · cases h
        · exact h
      have hA' : l ∉ l' :: A := by simp only [List.mem_cons, not_or]; exact ⟨hnal.1, hA⟩
      exact ih (A := l' :: A) hA' hnal.2 hmem'
    | access mu' l' =>
      have hmem' : TraceItem.dealloc l ∈ t := by
        rcases List.mem_cons.mp hmem with h | h
        · cases h
        · exact h
      simp only [Trace.allocd] at hnal
      exact Or.inr (ih hA hnal hmem')
    | dealloc l' =>
      rcases List.mem_cons.mp hmem with h | h
      · have : l' = l := by cases h; rfl
        exact Or.inl ⟨this.symm, hA, rfl⟩
      · simp only [Trace.allocd] at hnal
        exact Or.inr (ih hA hnal h)

/-- Non-interference forbids `s` from WRITING or DROPPING a cell `l` that `ts`
  reads (`.access .ro`); reads by `s` remain possible.  Pins a read's stored bit.
  Requires `l` not self-allocated by `s` (true when `l` pre-exists `s`). -/
theorem Trace.not_mutated_of_noninterfere {s ts : Trace} {l : Nat}
    (hsep : Trace.Noninterfere s ts) (hts : Trace.extTouchesMode ts l (.access .ro))
    (hnal : ¬ Trace.allocd s l) :
    ¬ (TraceItem.access .epsilon l ∈ s) ∧ ¬ (TraceItem.dealloc l ∈ s) := by
  refine ⟨fun hmem => ?_, fun hmem => ?_⟩
  · have hs : Trace.extTouchesMode s l (.access .epsilon) :=
      Trace.extTouchesFromMode_of_mem_access (by simp) hnal hmem
    exact absurd (hsep l _ _ hs hts).1 (by simp)
  · have hs : Trace.extTouchesMode s l .drop :=
      Trace.extTouchesFromMode_of_mem_dealloc (by simp) hnal hmem
    exact absurd (hsep l _ _ hs hts).1 (by simp)

/-- **Local diamond.**  A step of thread `e2` commutes past a full run of the
  separated thread `e1`: if `e2` steps `m1 → m2` (trace `ts`) and then `e1` runs
  `m2 → mb` (trace `s`), and the two traces are non-interfering, then `e1` can run
  FIRST from `m1` (to some `mc`) and the SAME `e2`-step then fires from `mc`,
  reaching the SAME `mb`.  This is the elementary reordering behind par
  sequentialization. -/
theorem BigStep.step_run_commute {ts s : Trace} {m1 m2 mb : Memory}
    {e1 e1res e2 e2' : Exp {}}
    (hstep : Step ts m1 e2 m2 e2')
    (hrun : BigStep m2 e1 s e1res mb)
    (hsep : Trace.Noninterfere s ts)
    (hwf1 : Exp.WfInHeap e1 m1.heap)
    (hwf2 : Exp.WfInHeap e2 m1.heap) :
    ∃ mc, BigStep m1 e1 s e1res mc ∧ Step ts mc e2 mb e2' := by
  induction hstep with
  | step_apply hlk =>
    exact ⟨mb, hrun, Step.step_apply (BigStep.val_preserved hrun hlk)⟩
  | step_invoke hlkx hlky =>
    have hnal : ¬ Trace.allocd s _ := fun ha => by
      have := BigStep.alloc_fresh hrun ha; rw [hlkx] at this; cases this
    have hntsx : ¬ Trace.touched s _ :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    exact ⟨mb, hrun,
      Step.step_invoke (BigStep.untouched_preserved hrun (by rw [hlkx]; simp) hntsx ▸ hlkx)
        (BigStep.val_preserved hrun hlky)⟩
  | step_tapply hlk =>
    exact ⟨mb, hrun, Step.step_tapply (BigStep.val_preserved hrun hlk)⟩
  | step_capply hlk =>
    exact ⟨mb, hrun, Step.step_capply (BigStep.val_preserved hrun hlk)⟩
  | step_unwrap hlk =>
    exact ⟨mb, hrun, Step.step_unwrap (BigStep.val_preserved hrun hlk)⟩
  | step_cond_var_true hlk =>
    exact ⟨mb, hrun, Step.step_cond_var_true (BigStep.val_preserved hrun hlk)⟩
  | step_cond_var_false hlk =>
    exact ⟨mb, hrun, Step.step_cond_var_false (BigStep.val_preserved hrun hlk)⟩
  | step_read hlkx hlky =>
    have hnal : ¬ Trace.allocd s _ := fun ha => by
      have := BigStep.alloc_fresh hrun ha; rw [hlky] at this; cases this
    obtain ⟨hw, hd⟩ := Trace.not_mutated_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) hnal
    exact ⟨mb, hrun,
      Step.step_read (BigStep.val_preserved hrun hlkx)
        (BigStep.unmutated_preserved hrun (by rw [hlky]; simp) hw hd ▸ hlky)⟩
  | step_write_true hx hy =>
    rename_i x m0 y b0 hv R
    have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
    have hcx : (m0.update_mcell x true .live ⟨_, hx⟩).lookup x =
        some (Cell.capability (.mcell true .live)) := by
      simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
    have hnal : ¬ Trace.allocd s x := fun ha => by
      have := BigStep.alloc_fresh hrun ha
      rw [show (m0.update_mcell x true .live ⟨_, hx⟩).lookup x = _ from hcx] at this; cases this
    have hntsx : ¬ Trace.touched s x :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    obtain ⟨mc, run, ag, cpres⟩ :=
      hrun.frame_off ⟨_, hcx⟩ ⟨_, hx⟩
        (fun l hl => Memory.update_mcell_lookup_ne hl) hntsx hwf1
    have mcx : mc.lookup x = some (Cell.capability (.mcell b0 .live)) := cpres.trans hx
    have mcy : mc.lookup y = some (Cell.val ⟨.btrue, hv, R⟩) :=
      (ag y hyx).symm.trans
        (BigStep.val_preserved hrun (by rw [Memory.update_mcell_lookup_ne hyx]; exact hy))
    have hmb : mc.update_mcell x true .live ⟨_, mcx⟩ = mb := by
      apply Memory.ext_lookup; intro l
      by_cases hlx : l = x
      · subst hlx
        rw [show (mc.update_mcell l true .live ⟨_, mcx⟩).lookup l
                = some (Cell.capability (.mcell true .live)) from by
              simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true],
            BigStep.untouched_preserved hrun (by rw [hcx]; simp) hntsx, hcx]
      · rw [Memory.update_mcell_lookup_ne hlx, ag l hlx]
    exact ⟨mc, run, hmb ▸ Step.step_write_true mcx mcy⟩
  | step_write_false hx hy =>
    rename_i x m0 y b0 hv R
    have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
    have hcx : (m0.update_mcell x false .live ⟨_, hx⟩).lookup x =
        some (Cell.capability (.mcell false .live)) := by
      simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true]
    have hnal : ¬ Trace.allocd s x := fun ha => by
      have := BigStep.alloc_fresh hrun ha
      rw [show (m0.update_mcell x false .live ⟨_, hx⟩).lookup x = _ from hcx] at this; cases this
    have hntsx : ¬ Trace.touched s x :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    obtain ⟨mc, run, ag, cpres⟩ :=
      hrun.frame_off ⟨_, hcx⟩ ⟨_, hx⟩
        (fun l hl => Memory.update_mcell_lookup_ne hl) hntsx hwf1
    have mcx : mc.lookup x = some (Cell.capability (.mcell b0 .live)) := cpres.trans hx
    have mcy : mc.lookup y = some (Cell.val ⟨.bfalse, hv, R⟩) :=
      (ag y hyx).symm.trans
        (BigStep.val_preserved hrun (by rw [Memory.update_mcell_lookup_ne hyx]; exact hy))
    have hmb : mc.update_mcell x false .live ⟨_, mcx⟩ = mb := by
      apply Memory.ext_lookup; intro l
      by_cases hlx : l = x
      · subst hlx
        rw [show (mc.update_mcell l false .live ⟨_, mcx⟩).lookup l
                = some (Cell.capability (.mcell false .live)) from by
              simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_true],
            BigStep.untouched_preserved hrun (by rw [hcx]; simp) hntsx, hcx]
      · rw [Memory.update_mcell_lookup_ne hlx, ag l hlx]
    exact ⟨mc, run, hmb ▸ Step.step_write_false mcx mcy⟩
  | step_alloc hlk hfresh =>
    rename_i l m0 x b hv R
    have hcl : (m0.extend_mcell l b hfresh).lookup l =
        some (Cell.capability (.mcell b .live)) := Memory.extend_mcell_lookup hfresh
    obtain ⟨mc, run, ag, cpres, hnt⟩ :=
      hrun.frame_off_fresh ⟨_, hcl⟩ hfresh
        (fun k hk => by
          simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hk]) hwf1
    have mcx : mc.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩) :=
      BigStep.val_preserved run hlk
    have hmb : mc.extend_mcell l b cpres = mb := by
      apply Memory.ext_lookup; intro k
      by_cases hkl : k = l
      · subst hkl
        rw [Memory.extend_mcell_lookup cpres,
            BigStep.untouched_preserved hrun (by rw [hcl]; simp) hnt, hcl]
      · rw [show (mc.extend_mcell l b cpres).lookup k = mc.lookup k from by
              simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hkl],
            ag k hkl]
    exact ⟨mc, run, hmb ▸ Step.step_alloc mcx cpres⟩
  | step_drop hx =>
    rename_i x m0 b0
    have hcx : (m0.drop_mcell x ⟨_, hx⟩).lookup x =
        some (Cell.capability (.mcell false .dead)) := by
      simp only [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_true]
    have hnal : ¬ Trace.allocd s x := fun ha => by
      have := BigStep.alloc_fresh hrun ha
      rw [show (m0.drop_mcell x ⟨_, hx⟩).lookup x = _ from hcx] at this; cases this
    have hntsx : ¬ Trace.touched s x :=
      Trace.not_touched_of_noninterfere hsep (Or.inl ⟨rfl, by simp, rfl⟩) (by simp) hnal
    obtain ⟨mc, run, ag, cpres⟩ :=
      hrun.frame_off ⟨_, hcx⟩ ⟨_, hx⟩
        (fun l hl => Memory.drop_mcell_lookup_ne hl) hntsx hwf1
    have mcx : mc.lookup x = some (Cell.capability (.mcell b0 .live)) := cpres.trans hx
    have hmb : mc.drop_mcell x ⟨_, mcx⟩ = mb := by
      apply Memory.ext_lookup; intro l
      by_cases hlx : l = x
      · subst hlx
        rw [show (mc.drop_mcell l ⟨_, mcx⟩).lookup l
                = some (Cell.capability (.mcell false .dead)) from by
              simp only [Memory.lookup, Memory.drop_mcell, Heap.update_cell, if_true],
            BigStep.untouched_preserved hrun (by rw [hcx]; simp) hntsx, hcx]
      · rw [Memory.drop_mcell_lookup_ne hlx, ag l hlx]
    exact ⟨mc, run, hmb ▸ Step.step_drop mcx⟩
  | step_ctx_letin hinner ih =>
    obtain ⟨mc, run, stepc⟩ := ih hrun hsep hwf1 (Exp.wf_inv_letin hwf2).1
    exact ⟨mc, run, Step.step_ctx_letin stepc⟩
  | step_ctx_unpack hinner ih =>
    obtain ⟨mc, run, stepc⟩ := ih hrun hsep hwf1 (Exp.wf_inv_unpack hwf2).1
    exact ⟨mc, run, Step.step_ctx_unpack stepc⟩
  | step_par_left hinner ht hni ih =>
    cases hwf2 with
    | wf_par hwfC1 hwfC2 hwfa hwfb =>
      obtain ⟨mc, run, stepc⟩ := ih hrun hsep hwf1 hwfa
      -- reachability is subsumption-invariant (`mc ⊒ m1`), so the `m1` guards transport to `mc`.
      have hr1 := CaptureSet.reachability_monotonic run.subsumes _ hwfC1
      have hr2 := CaptureSet.reachability_monotonic run.subsumes _ hwfC2
      exact ⟨mc, run, Step.step_par_left stepc (by rw [hr1]; exact ht)
        (by rw [hr1, hr2]; exact hni)⟩
  | step_par_right ht hni hinner ih =>
    cases hwf2 with
    | wf_par hwfC1 hwfC2 hwfa hwfb =>
      obtain ⟨mc, run, stepc⟩ := ih hrun hsep hwf1 hwfb
      have hr1 := CaptureSet.reachability_monotonic run.subsumes _ hwfC1
      have hr2 := CaptureSet.reachability_monotonic run.subsumes _ hwfC2
      exact ⟨mc, run, Step.step_par_right (by rw [hr2]; exact ht)
        (by rw [hr1, hr2]; exact hni) stepc⟩
  | step_par_join h1 h2 =>
    exact ⟨mb, hrun, Step.step_par_join h1 h2⟩
  | step_rename =>
    exact ⟨mb, hrun, Step.step_rename⟩
  | step_lift hv hwf hfresh =>
    rename_i v m0 _ l
    have hcl : (m0.extend l ⟨v, hv, compute_reachability m0.heap v hv⟩ hwf rfl hfresh).lookup l
        = some (Cell.val ⟨v, hv, compute_reachability m0.heap v hv⟩) := by
      simp only [Memory.lookup, Memory.extend, Heap.extend_lookup_eq]
    obtain ⟨mc, run, ag, cpres, hnt⟩ :=
      hrun.frame_off_absent (by rw [hcl]; simp) hfresh
        (fun k hk => by
          simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg hk]) hwf1
    have hwfc : v.WfInHeap mc.heap := Exp.wf_monotonic (BigStep.subsumes run) hwf
    have hreach : compute_reachability mc.heap v hv = compute_reachability m0.heap v hv :=
      compute_reachability_monotonic (BigStep.subsumes run) v hv hwf
    have hmbl : (mc.extend l ⟨v, hv, compute_reachability mc.heap v hv⟩ hwfc rfl cpres).lookup l
        = some (Cell.val ⟨v, hv, compute_reachability mc.heap v hv⟩) := by
      simp only [Memory.lookup, Memory.extend, Heap.extend_lookup_eq]
    have hmb : mc.extend l ⟨v, hv, compute_reachability mc.heap v hv⟩ hwfc rfl cpres = mb := by
      apply Memory.ext_lookup; intro k
      by_cases hkl : k = l
      · subst hkl
        rw [hmbl, hreach, BigStep.untouched_preserved hrun (by rw [hcl]; simp) hnt, hcl]
      · rw [show (mc.extend l ⟨v, hv, compute_reachability mc.heap v hv⟩ hwfc rfl cpres).lookup k
                = mc.lookup k from by
              simp only [Memory.lookup, Memory.extend, Heap.extend, if_neg hkl],
            ag k hkl]
    exact ⟨mc, run, hmb ▸ Step.step_lift hv hwfc cpres⟩
  | step_unpack =>
    exact ⟨mb, hrun, Step.step_unpack⟩

/-- A freshly-appeared CAPABILITY cell was allocated within the trace.  Only
  `extend_mcell` adds capabilities (`extend_val` adds non-capability vals; the
  other heap ops never grow the domain), so a capability present in `m'` but
  absent in `m` traces to an `.alloc` event.  (The capability analogue of
  `live_appears_allocd`, but needing no liveness.) -/
theorem BigStep.appears_allocd_of_cap {m : Memory} {e : Exp {}} {t v m' l c}
    (hbs : BigStep m e t v m') (hl : m.lookup l = none)
    (hl' : m'.lookup l = some (.capability c)) : Trace.allocd t l := by
  induction hbs generalizing c with
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
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih =>
    exact ih hl hl'
  | bs_par hbs1 hbs2 ih1 ih2 =>
    rename_i m1 _ _ _
    refine Trace.allocd_append.mpr ?_
    rcases hsrc : m1.lookup l with _ | c0
    · exact Or.inr (ih2 hsrc hl')
    · have hcy := Memory.lookup_down hbs2.subsumes hsrc hl'
      cases c0 with
      | val vv => simp [Cell.subsumes] at hcy
      | masked => simp [Cell.subsumes] at hcy
      | capability cc => exact Or.inl (ih1 hl hsrc)
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    rename_i _ _ _ _ _ _ m1 _ vval l'
    refine Trace.allocd_append.mpr ?_
    rcases hsrc : (m1.extend_val l' ⟨vval, hv, compute_reachability m1.heap vval hv⟩
        hwf_v rfl hfresh).lookup l with _ | c0
    · exact Or.inr (ih2 hsrc hl')
    · have hcy := Memory.lookup_down hbs2.subsumes hsrc hl'
      cases c0 with
      | val vv => simp [Cell.subsumes] at hcy
      | masked => simp [Cell.subsumes] at hcy
      | capability cc => exact Or.inl (ih1 hl (Memory.extend_val_lookup_cap hsrc))
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    rename_i _ _ _ _ _ _ m1 _ _
    refine Trace.allocd_append.mpr ?_
    rcases hsrc : m1.lookup l with _ | c0
    · exact Or.inr (ih2 hsrc hl')
    · have hcy := Memory.lookup_down hbs2.subsumes hsrc hl'
      cases c0 with
      | val vv => simp [Cell.subsumes] at hcy
      | masked => simp [Cell.subsumes] at hcy
      | capability cc => exact Or.inl (ih1 hl hsrc)
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    rename_i _ _ _ _ _ _ m1 _ _ _
    refine Trace.allocd_append.mpr ?_
    rcases hsrc : m1.lookup l with _ | c0
    · exact Or.inr (ih2 hsrc hl')
    · have hcy := Memory.lookup_down hbs2.subsumes hsrc hl'
      cases c0 with
      | val vv => simp [Cell.subsumes] at hcy
      | masked => simp [Cell.subsumes] at hcy
      | capability cc => exact Or.inl (ih1 hl hsrc)

/-- A CAPABILITY cell stays a capability upward along subsumption (subsumption only
  changes mcell liveness, never cell KIND). -/
theorem Memory.cap_subsumes_up {m1 m2 : Memory} {l : Nat} {c0 : CapabilityInfo}
    (hsub : m2.subsumes m1) (h1 : m1.lookup l = some (.capability c0)) :
    ∃ c', m2.lookup l = some (.capability c') := by
  obtain ⟨c', h2, hsubc⟩ := hsub l _ h1
  cases c' with
  | capability cc => exact ⟨cc, h2⟩
  | val _ => simp [Cell.subsumes] at hsubc
  | masked => simp [Cell.subsumes] at hsubc

/-- Every location a `BigStep` trace ACCESSES or DEALLOCATES is a capability cell in
  the final memory.  This is the operational counterpart of "well-typed readers point
  to mcells": `bs_read`/`bs_write`/`bs_drop` require a (live or just-dropped) mcell at
  the target, `bs_invoke` a basic capability — all capabilities; the recursive/letin
  cases carry the fact upward by `cap_subsumes_up`.  It lets `unpack` discharge the
  fresh-witness exemption from the run (`trace_cells_cap`) rather than from a
  capability-reachability invariant the wf cannot express. -/
theorem BigStep.trace_cells_cap {m : Memory} {e : Exp {}} {t v m'}
    (hbs : BigStep m e t v m') :
    ∀ l, Trace.touched t l → ∃ c, m'.lookup l = some (.capability c) := by
  induction hbs with
  | bs_pack | bs_val _ | bs_var | bs_wrap | bs_alloc _ _ =>
    intro l h; simp only [Trace.touched] at h
  | bs_invoke hlkx _ =>
    intro l h; simp only [Trace.touched, or_false] at h; subst h; exact ⟨_, hlkx⟩
  | bs_read _ hlky =>
    intro l h; simp only [Trace.touched, or_false] at h; subst h; exact ⟨_, hlky⟩
  | bs_write_true hx _ =>
    intro l h; simp only [Trace.touched, or_false] at h; subst h
    exact ⟨.mcell true .live, by simp [Memory.lookup, Memory.update_mcell, Heap.update_cell]⟩
  | bs_write_false hx _ =>
    intro l h; simp only [Trace.touched, or_false] at h; subst h
    exact ⟨.mcell false .live, by simp [Memory.lookup, Memory.update_mcell, Heap.update_cell]⟩
  | bs_drop hx =>
    intro l h; simp only [Trace.touched, or_false] at h; subst h
    exact ⟨.mcell false .dead, by simp [Memory.lookup, Memory.drop_mcell, Heap.update_cell]⟩
  | bs_apply _ _ ih | bs_tapply _ _ ih | bs_capply _ _ ih | bs_unwrap _ _ ih
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih =>
    exact ih
  | bs_par hbs1 hbs2 ih1 ih2 =>
    intro l h
    rw [Trace.touched_append] at h
    rcases h with h1 | h2
    · obtain ⟨c, hc⟩ := ih1 l h1; exact Memory.cap_subsumes_up hbs2.subsumes hc
    · exact ih2 l h2
  | bs_letin_val hbs1 hv hwf_v hfresh hbs2 ih1 ih2 =>
    intro l h
    rw [Trace.touched_append] at h
    rcases h with h1 | h2
    · obtain ⟨c, hc⟩ := ih1 l h1
      exact Memory.cap_subsumes_up
        (Memory.subsumes_trans hbs2.subsumes
          (Memory.extend_val_subsumes _ _ _ hwf_v rfl hfresh)) hc
    · exact ih2 l h2
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    intro l h
    rw [Trace.touched_append] at h
    rcases h with h1 | h2
    · obtain ⟨c, hc⟩ := ih1 l h1; exact Memory.cap_subsumes_up hbs2.subsumes hc
    · exact ih2 l h2
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    intro l h
    rw [Trace.touched_append] at h
    rcases h with h1 | h2
    · obtain ⟨c, hc⟩ := ih1 l h1; exact Memory.cap_subsumes_up hbs2.subsumes hc
    · exact ih2 l h2

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
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih =>
    exact ih hl hl'
  | bs_par hbs1 hbs2 ih1 ih2 =>
    rename_i m1 _ _ _
    refine Trace.allocd_append.mpr ?_
    rcases hsrc : m1.lookup l with _ | c
    · exact Or.inr (ih2 hsrc hl')
    · obtain ⟨b1, hc'⟩ := Memory.mcell_lookup_down hbs2.subsumes hsrc hl'
      exact Or.inl (ih1 hl hc')
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

/-! ## Budget bounds for steps (the `par`-adequacy infrastructure)

  The remaining `par`-adequacy proofs need to bound the trace of a *single step*
  of a branch by that branch's static budget.  The device is a reusable predicate
  `RobustBudget m e C` (the `Safe.par` `hb`-field, named), a handful of
  *sub-budget* lemmas (the budget for a compound `e` descends to its head
  sub-term), and `step_traceOk` (a step's trace is `TraceOk`-bounded), proved by
  induction on the step. -/

/-- `TraceOkFrom` is closed under taking a prefix: the suffix only ever ADDS
  events that need authority, so dropping it cannot break `TraceOk`-ness. -/
theorem TraceOkFrom.prefix {C : CapabilitySet} :
  ∀ {A : List Nat} {t1 t2 : Trace},
    TraceOkFrom C A (t1 ++ t2) -> TraceOkFrom C A t1 := by
  intro A t1 t2 h
  induction t1 generalizing A with
  | nil => exact TraceOkFrom.nil
  | cons it t1 ih =>
    rw [List.cons_append] at h
    cases it with
    | alloc l => cases h with | alloc h => exact TraceOkFrom.alloc (ih h)
    | access mu l => cases h with | access hc h => exact TraceOkFrom.access hc (ih h)
    | dealloc l => cases h with | dealloc hc h => exact TraceOkFrom.dealloc hc (ih h)

theorem TraceOk.prefix {C : CapabilitySet} {t1 t2 : Trace}
  (h : TraceOk (t1 ++ t2) C) : TraceOk t1 C :=
  TraceOkFrom.prefix h

/-- The capability set covering EVERY mode (`.access .epsilon`, hence also `.ro`, and
  `.drop`) at each location in `A`.  Used to absorb a `TraceOkFrom` allocated-set
  exemption into the budget: a cell freshly allocated by a step is, for the reduct,
  an extra budget capability rather than an exemption. -/
def capsOf : List Nat -> CapabilitySet
| [] => .empty
| l :: A => (.cap (.access .epsilon) l) ∪ ((.cap .drop l) ∪ capsOf A)

/-- Membership in `capsOf A` is membership in `A`. -/
theorem capsOf_hasmem {A : List Nat} {l : Nat} {cm : CapMode}
    (h : (capsOf A).hasmem cm l) : l ∈ A := by
  induction A with
  | nil => exact absurd h CapabilitySet.not_hasmem_empty
  | cons l' A ih =>
    rw [capsOf] at h
    rcases CapabilitySet.hasmem_union_iff.mp h with h1 | h2
    · cases h1; exact List.mem_cons_self ..
    · rcases CapabilitySet.hasmem_union_iff.mp h2 with h3 | h4
      · cases h3; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h4)

/-- `capsOf A` covers any mode at every location of `A`. -/
theorem capsOf_covers {A : List Nat} {l : Nat} {cm : CapMode} (h : l ∈ A) :
    (capsOf A).covers cm l := by
  induction A with
  | nil => simp at h
  | cons l' A ih =>
    rcases List.mem_cons.mp h with rfl | h
    · cases cm with
      | access mu =>
        refine CapabilitySet.covers_union_left (.here (.access ?_))
        cases mu with
        | epsilon => exact Mutability.Le.refl
        | ro => exact Mutability.Le.ro_le
      | drop =>
        exact CapabilitySet.covers_union_right (CapabilitySet.covers_union_left (.here .drop))
    · exact CapabilitySet.covers_union_right (CapabilitySet.covers_union_right (ih h))

/-- **Absorb a tail allocated-set exemption into the budget.**  `TraceOkFrom C (D ++ A) t`
  becomes `TraceOkFrom (C ∪ capsOf A) D t`: the `A`-exemptions (the step's fresh cells)
  are re-bucketed as budget caps (`capsOf A`), while the trace's own running allocations
  `D` stay exemptions.  This converts the step's allocations (`split_append`'s
  exemptions) into budget growth for the reduct. -/
theorem TraceOkFrom.absorb_exempt_aux {C : CapabilitySet} {A : List Nat} :
  ∀ {D : List Nat} {t : Trace},
    TraceOkFrom C (D ++ A) t -> TraceOkFrom (C ∪ capsOf A) D t := by
  intro D t
  induction t generalizing D with
  | nil => intro _; exact TraceOkFrom.nil
  | cons it t ih =>
    intro h
    cases it with
    | alloc l =>
      cases h with
      | alloc h =>
        exact TraceOkFrom.alloc (ih (D := l :: D)
          (by simpa only [List.cons_append] using h))
    | access mu l =>
      cases h with
      | access hc h =>
        refine TraceOkFrom.access ?_ (ih h)
        rcases hc with hcov | hin
        · exact Or.inl (CapabilitySet.covers_union_left hcov)
        · rcases List.mem_append.mp hin with hD | hA
          · exact Or.inr hD
          · exact Or.inl (CapabilitySet.covers_union_right (capsOf_covers hA))
    | dealloc l =>
      cases h with
      | dealloc hc h =>
        refine TraceOkFrom.dealloc ?_ (ih h)
        rcases hc with hcov | hin
        · exact Or.inl (CapabilitySet.covers_union_left hcov)
        · rcases List.mem_append.mp hin with hD | hA
          · exact Or.inr hD
          · exact Or.inl (CapabilitySet.covers_union_right (capsOf_covers hA))

/-- `TraceOkFrom C A t → TraceOk t (C ∪ capsOf A)`: absorb the whole exemption set. -/
theorem TraceOkFrom.absorb_exempt {C : CapabilitySet} {A : List Nat} {t : Trace}
    (h : TraceOkFrom C A t) : TraceOk t (C ∪ capsOf A) :=
  TraceOkFrom.absorb_exempt_aux (D := []) (by simpa using h)

/-- A singleton capability at a location NOT in `C` is non-interfering with `C`:
  the locations are distinct, so every overlap check is `ni_disj`. -/
theorem CapabilitySet.noninterference_cap_fresh {C : CapabilitySet} {cm : CapMode}
    {l : Nat} (h : ∀ mu', ¬ C.hasmem mu' l) :
    CapabilitySet.Noninterference (.cap cm l) C := by
  induction C with
  | empty => exact CapabilitySet.Noninterference.ni_symm CapabilitySet.Noninterference.ni_empty
  | cap cm' l' =>
    refine CapabilitySet.Noninterference.ni_disj (fun hle => ?_)
    exact h cm' (hle ▸ CapabilitySet.hasmem.here)
  | union C1 C2 ih1 ih2 =>
    refine CapabilitySet.Noninterference.ni_symm (CapabilitySet.Noninterference.ni_union ?_ ?_)
    · exact CapabilitySet.Noninterference.ni_symm
        (ih1 (fun mu' hm => h mu' (CapabilitySet.hasmem.left hm)))
    · exact CapabilitySet.Noninterference.ni_symm
        (ih2 (fun mu' hm => h mu' (CapabilitySet.hasmem.right hm)))

/-- `capsOf A` is non-interfering with `C` when no `A`-location is in `C`. -/
theorem CapabilitySet.noninterference_capsOf_fresh {C : CapabilitySet} {A : List Nat}
    (h : ∀ l, l ∈ A -> ∀ mu', ¬ C.hasmem mu' l) :
    CapabilitySet.Noninterference (capsOf A) C := by
  induction A with
  | nil => exact CapabilitySet.Noninterference.ni_empty
  | cons l' A ih =>
    refine CapabilitySet.Noninterference.ni_union
      (CapabilitySet.noninterference_cap_fresh (h l' (List.mem_cons_self ..)))
      (CapabilitySet.Noninterference.ni_union
        (CapabilitySet.noninterference_cap_fresh (h l' (List.mem_cons_self ..)))
        (ih (fun l hl mu' => h l (List.mem_cons_of_mem _ hl) mu')))

/-! ### Coincidence of the grown annotation's reachability with `capsOf`

  The `par` annotation grows by `CaptureSet.growByAllocs` as a branch allocates; the
  matching `Safe.par` budget grows by `capsOf`.  For a live mcell `l`, the full-authority
  capture `.var (.M .epsilon) (.free l)` reaches `.cap (.access .epsilon) l` and
  `.var .drop (.free l)` reaches `.cap .drop l`, so the grown annotation's reachability
  and `C.reachability m ∪ capsOf (allocList t)` mutually contain each other. -/

/-- Reachability of an access-mode capture of a live capability cell. -/
theorem reachability_var_eps {m : Memory} {l : Nat} {info : CapabilityInfo}
    (h : m.heap l = some (.capability info)) :
    (CaptureSet.var (.M .epsilon) (.free l) : CaptureSet {}).reachability m
      = .cap (.access .epsilon) l := by
  change (reachability_of_loc m.heap l).applyAccess (.M .epsilon) = _
  simp only [reachability_of_loc, h, CapabilitySet.singleton, CapabilitySet.applyAccess,
    CapabilitySet.applyMut]

/-- Reachability of a drop-mode capture of a live capability cell. -/
theorem reachability_var_drop {m : Memory} {l : Nat} {info : CapabilityInfo}
    (h : m.heap l = some (.capability info)) :
    (CaptureSet.var .drop (.free l) : CaptureSet {}).reachability m = .cap .drop l := by
  change (reachability_of_loc m.heap l).applyAccess .drop = _
  simp only [reachability_of_loc, h, CapabilitySet.singleton, CapabilitySet.applyAccess,
    CapabilitySet.to_drop]

/-- The cells freshly allocated by a single `SeqStep` are live mcells in the post-memory
  (a strengthening of `step_allocd_present`). -/
theorem step_allocd_mcell {t : Trace} {m1 e1 m2 e2 : _} {l : Nat}
    (hstep : SeqStep t m1 e1 m2 e2) (hal : Trace.allocd t l) :
    ∃ info, m2.heap l = some (.capability info) := by
  induction hstep with
  | step_apply | step_invoke _ _ | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write_true _ _ | step_write_false _ _ | step_drop _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.allocd] at hal
  | step_alloc _ hfresh =>
    simp only [Trace.allocd, or_false] at hal; subst hal
    exact ⟨_, Memory.extend_mcell_lookup hfresh⟩
  | step_ctx_letin _ ih | step_ctx_unpack _ ih | step_par_left _ ih => exact ih hal
  | step_par_right _ _ ih => exact ih hal

/-- The original annotation's reachability is contained in the grown one (growth only
  ADDS captures, and reachability is monotone). -/
theorem growByAllocs_reachability_ge {m : Memory} :
    ∀ {t : Trace} {C : CaptureSet {}}, C.reachability m ⊆ (C.growByAllocs t).reachability m := by
  intro t
  induction t with
  | nil => intro C; exact CapabilitySet.Subset.refl
  | cons it t ih =>
    intro C
    cases it with
    | alloc l =>
      refine CapabilitySet.Subset.trans ?_ ih
      exact CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right
        CapabilitySet.Subset.union_right_right
    | access mu l => exact ih
    | dealloc l => exact ih

/-- Reachability distributes over capture-set union (definitional). -/
@[simp] theorem CaptureSet.reachability_union {A B : CaptureSet {}} {m : Memory} :
    (A ∪ B).reachability m = A.reachability m ∪ B.reachability m := rfl

/-- The freshly-allocated cells' caps are contained in the grown annotation's reachability
  (each fresh cell joins the annotation at FULL authority). -/
theorem capsOf_subset_growByAllocs_reachability {m : Memory} :
    ∀ {t : Trace} {C : CaptureSet {}},
      (∀ l, l ∈ Trace.allocList t → ∃ info, m.heap l = some (.capability info)) →
      capsOf (Trace.allocList t) ⊆ (C.growByAllocs t).reachability m := by
  intro t
  induction t with
  | nil => intro C _; exact CapabilitySet.Subset.empty
  | cons it t ih =>
    intro C hlive
    cases it with
    | alloc l =>
      obtain ⟨info, hinfo⟩ := hlive l (by simp [Trace.allocList])
      have hlive' : ∀ l', l' ∈ Trace.allocList t → ∃ info, m.heap l' = some (.capability info) :=
        fun l' hl' => hlive l' (by simp only [Trace.allocList, List.mem_cons]; exact Or.inr hl')
      simp only [Trace.allocList, capsOf]
      refine CapabilitySet.Subset.union_left ?_ (CapabilitySet.Subset.union_left ?_ (ih hlive'))
      · rw [← reachability_var_eps hinfo]
        exact CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left
          (growByAllocs_reachability_ge (C := (CaptureSet.var (.M .epsilon) (.free l))
            ∪ ((CaptureSet.var .drop (.free l)) ∪ C)))
      · rw [← reachability_var_drop hinfo]
        exact CapabilitySet.Subset.trans
          (CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left
            CapabilitySet.Subset.union_right_right)
          (growByAllocs_reachability_ge (C := (CaptureSet.var (.M .epsilon) (.free l))
            ∪ ((CaptureSet.var .drop (.free l)) ∪ C)))
    | access mu l => exact ih hlive
    | dealloc l => exact ih hlive

/-- The grown annotation's reachability adds nothing beyond `capsOf` of the fresh cells. -/
theorem growByAllocs_reachability_le {m : Memory} :
    ∀ {t : Trace} {C : CaptureSet {}},
      (∀ l, l ∈ Trace.allocList t → ∃ info, m.heap l = some (.capability info)) →
      (C.growByAllocs t).reachability m ⊆ C.reachability m ∪ capsOf (Trace.allocList t) := by
  intro t
  induction t with
  | nil => intro C _; exact CapabilitySet.Subset.union_right_left
  | cons it t ih =>
    intro C hlive
    cases it with
    | alloc l =>
      obtain ⟨info, hinfo⟩ := hlive l (by simp [Trace.allocList])
      have hlive' : ∀ l', l' ∈ Trace.allocList t → ∃ info, m.heap l' = some (.capability info) :=
        fun l' hl' => hlive l' (by simp only [Trace.allocList, List.mem_cons]; exact Or.inr hl')
      refine CapabilitySet.Subset.trans
        (ih (C := (CaptureSet.var (.M .epsilon) (.free l))
          ∪ ((CaptureSet.var .drop (.free l)) ∪ C)) hlive') ?_
      simp only [Trace.allocList, capsOf, CaptureSet.reachability_union,
        reachability_var_eps hinfo, reachability_var_drop hinfo]
      -- goal: (cap_e ∪ (cap_d ∪ C.reach)) ∪ caps ⊆ C.reach ∪ (cap_e ∪ (cap_d ∪ caps))
      refine CapabilitySet.Subset.union_left
        (CapabilitySet.Subset.union_left ?_ (CapabilitySet.Subset.union_left ?_ ?_)) ?_
      · exact CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left
          CapabilitySet.Subset.union_right_right
      · exact CapabilitySet.Subset.trans
          (CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_left
            CapabilitySet.Subset.union_right_right)
          CapabilitySet.Subset.union_right_right
      · exact CapabilitySet.Subset.union_right_left
      · exact CapabilitySet.Subset.trans
          (CapabilitySet.Subset.trans CapabilitySet.Subset.union_right_right
            CapabilitySet.Subset.union_right_right)
          CapabilitySet.Subset.union_right_right
    | access mu l => exact ih hlive
    | dealloc l => exact ih hlive

/-- Well-formedness of a grown annotation: every cell `growByAllocs` adds is freshly
  allocated, hence present in the post-trace memory.  The base `C` must be well-formed in
  that same (final) memory (the allocations are not present in the start memory). -/
theorem CaptureSet.growByAllocs_wf {m : Memory} :
    ∀ {t : Trace} {C : CaptureSet {}},
      CaptureSet.WfInHeap C m.heap →
      (∀ l, l ∈ Trace.allocList t → m.heap l ≠ none) →
      CaptureSet.WfInHeap (C.growByAllocs t) m.heap := by
  intro t
  induction t with
  | nil => intro C hwf _; exact hwf
  | cons it t ih =>
    intro C hwf hpres
    cases it with
    | alloc l =>
      have hl : m.heap l ≠ none := hpres l (by simp [Trace.allocList])
      cases hh : m.heap l with
      | none => exact absurd hh hl
      | some val =>
        refine ih ?_ (fun l' hl' =>
          hpres l' (by simp only [Trace.allocList, List.mem_cons]; exact Or.inr hl'))
        exact CaptureSet.WfInHeap.wf_union (CaptureSet.WfInHeap.wf_var_free hh)
          (CaptureSet.WfInHeap.wf_union (CaptureSet.WfInHeap.wf_var_free hh) hwf)
    | access mu l =>
      exact ih hwf (fun l' hl' => hpres l' (by simpa only [Trace.allocList] using hl'))
    | dealloc l =>
      exact ih hwf (fun l' hl' => hpres l' (by simpa only [Trace.allocList] using hl'))

/-- **Link maintenance under a step.**  When the budget grows by `capsOf` and the
  annotation by `growByAllocs` (in lockstep), the budget = annotation-reachability link
  (mutual `⊆`) is preserved.  Maintains `Safe.par`'s `hcov` field across a branch step. -/
theorem Safe.hcov_step {m1 m2 : Memory} {Cs1 : CaptureSet {}} {C1 : CapabilitySet} {t : Trace}
    (hsub21 : m2.subsumes m1) (hwfC1 : Cs1.WfInHeap m1.heap)
    (hlive : ∀ l, l ∈ Trace.allocList t → ∃ info, m2.heap l = some (.capability info))
    (hcov1 : C1 ⊆ Cs1.reachability m1 ∧ Cs1.reachability m1 ⊆ C1) :
    (C1 ∪ capsOf (Trace.allocList t)) ⊆ (Cs1.growByAllocs t).reachability m2 ∧
    (Cs1.growByAllocs t).reachability m2 ⊆ (C1 ∪ capsOf (Trace.allocList t)) := by
  have hmono : Cs1.reachability m2 = Cs1.reachability m1 :=
    CaptureSet.reachability_monotonic hsub21 Cs1 hwfC1
  constructor
  · refine CapabilitySet.Subset.union_left ?_ (capsOf_subset_growByAllocs_reachability hlive)
    refine CapabilitySet.Subset.trans hcov1.1 ?_
    rw [← hmono]; exact growByAllocs_reachability_ge
  · refine CapabilitySet.Subset.trans (growByAllocs_reachability_le hlive) ?_
    rw [hmono]
    exact CapabilitySet.Subset.union_left
      (CapabilitySet.Subset.trans hcov1.2 CapabilitySet.Subset.union_right_left)
      CapabilitySet.Subset.union_right_right

/-- The **robust budget** predicate: every `BigStep` run of `e` — from ANY memory
  `m' ⊒ m` — has its trace bounded by `C`.  This is exactly the `hb1`/`hb2` field
  of `Safe.par`, given a name so the bound can be threaded and transformed. -/
def RobustBudget (m : Memory) (e : Exp {}) (C : CapabilitySet) : Prop :=
  ∀ {m' : Memory} {t : Trace} {v : Exp {}} {m''},
    m'.subsumes m -> Exp.WfInHeap e m'.heap -> BigStep m' e t v m'' -> TraceOk t C

/-- Split off a prefix from `TraceOkFrom`: the suffix `t2` is `TraceOkFrom` with
  the prefix `t1`'s allocations added to the exemption set. -/
theorem TraceOkFrom.split_append {C : CapabilitySet} :
  ∀ {A : List Nat} {t1 t2 : Trace},
    TraceOkFrom C A (t1 ++ t2) -> TraceOkFrom C (Trace.allocList t1 ++ A) t2 := by
  intro A t1 t2 h
  induction t1 generalizing A with
  | nil => exact h
  | cons it t1 ih =>
    rw [List.cons_append] at h
    cases it with
    | alloc l =>
      cases h with
      | alloc h =>
        exact TraceOkFrom.mono_alloc (by
          intro x hx
          simp only [Trace.allocList, List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
          tauto) (ih h)
    | access mu l => cases h with | access _ h => exact ih h
    | dealloc l => cases h with | dealloc _ h => exact ih h

/-- A `TraceOkFrom` with extra exemptions `S` that the trace never TOUCHES is a
  `TraceOkFrom` without them: an access/dealloc covered only by an `S`-exemption
  would TOUCH that `S`-location, contradicting the hypothesis; so every event is
  covered by `C` or by an `A`-exemption. -/
theorem TraceOkFrom.drop_unused_exempt {C : CapabilitySet} {S : List Nat} :
  ∀ {A : List Nat} {t : Trace},
    TraceOkFrom C (S ++ A) t -> (∀ l, Trace.touched t l -> l ∉ S) ->
    TraceOkFrom C A t := by
  intro A t
  induction t generalizing A with
  | nil => intro _ _; exact TraceOkFrom.nil
  | cons it t ih =>
    intro h hnt
    cases it with
    | alloc l =>
      cases h with
      | alloc h =>
        refine TraceOkFrom.alloc (ih (A := l :: A) ?_ (fun l' h' => hnt l' (by
          simp only [Trace.touched]; exact h')))
        exact TraceOkFrom.mono_alloc (A := l :: (S ++ A)) (A' := S ++ l :: A)
          (by intro x hx; simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto) h
    | access mu l =>
      cases h with
      | access hc h =>
        have hnt_l : l ∉ S := hnt l (by simp only [Trace.touched]; tauto)
        refine TraceOkFrom.access ?_ (ih h (fun l' h' => hnt l' (by
          simp only [Trace.touched]; exact Or.inr h')))
        rcases hc with hcov | hin
        · exact Or.inl hcov
        · rcases List.mem_append.mp hin with hS | hA
          · exact absurd hS hnt_l
          · exact Or.inr hA
    | dealloc l =>
      cases h with
      | dealloc hc h =>
        have hnt_l : l ∉ S := hnt l (by simp only [Trace.touched]; tauto)
        refine TraceOkFrom.dealloc ?_ (ih h (fun l' h' => hnt l' (by
          simp only [Trace.touched]; exact Or.inr h')))
        rcases hc with hcov | hin
        · exact Or.inl hcov
        · rcases List.mem_append.mp hin with hS | hA
          · exact absurd hS hnt_l
          · exact Or.inr hA

/-- Order- and allocation-INDEPENDENT "touch": `l` is accessed (`cm = .access mu`)
  or dropped (`cm = .drop`) SOMEWHERE in `t`.  Unlike `extTouchesMode`, this does
  not consult the running allocation set, so it is invariant under permutation. -/
def Trace.touchesWith : Trace -> Nat -> CapMode -> Prop
| [], _, _ => False
| (.access mu l' :: t), l, cm => (l = l' ∧ cm = .access mu) ∨ Trace.touchesWith t l cm
| (.dealloc l' :: t), l, cm => (l = l' ∧ cm = .drop) ∨ Trace.touchesWith t l cm
| (.alloc _ :: t), l, cm => Trace.touchesWith t l cm

theorem Trace.touchesWith_append {t1 t2 : Trace} {l : Nat} {cm : CapMode} :
    Trace.touchesWith (t1 ++ t2) l cm <->
      Trace.touchesWith t1 l cm ∨ Trace.touchesWith t2 l cm := by
  induction t1 with
  | nil => simp [Trace.touchesWith]
  | cons it t1 ih =>
    cases it <;> simp only [List.cons_append, Trace.touchesWith, ih, or_assoc]

/-- An external touch (mode-carrying) is in particular a `touchesWith`. -/
theorem Trace.touchesWith_of_extTouchesFromMode {A : List Nat} {l : Nat} {cm : CapMode} :
    ∀ {t : Trace}, Trace.extTouchesFromMode A l cm t -> Trace.touchesWith t l cm := by
  intro t
  induction t generalizing A with
  | nil => intro h; simp only [Trace.extTouchesFromMode] at h
  | cons it t ih =>
    cases it with
    | alloc l' => intro h; exact ih h
    | access mu l' =>
      intro h
      rcases h with ⟨hl, _, hcm⟩ | h
      · exact Or.inl ⟨hl, hcm⟩
      · exact Or.inr (ih h)
    | dealloc l' =>
      intro h
      rcases h with ⟨hl, _, hcm⟩ | h
      · exact Or.inl ⟨hl, hcm⟩
      · exact Or.inr (ih h)

theorem Trace.touchesWith_of_extTouchesMode {t : Trace} {l : Nat} {cm : CapMode}
    (h : Trace.extTouchesMode t l cm) : Trace.touchesWith t l cm :=
  Trace.touchesWith_of_extTouchesFromMode h

/-- A `touchesWith` is a `touched` (forgetting the mode). -/
theorem Trace.touched_of_touchesWith {t : Trace} {l : Nat} {cm : CapMode}
    (h : Trace.touchesWith t l cm) : Trace.touched t l := by
  induction t with
  | nil => simp only [Trace.touchesWith] at h
  | cons it t ih =>
    cases it with
    | alloc l' => exact ih h
    | access mu l' => rcases h with ⟨hl, _⟩ | h; · exact Or.inl hl
                      · exact Or.inr (ih h)
    | dealloc l' => rcases h with ⟨hl, _⟩ | h; · exact Or.inl hl
                    · exact Or.inr (ih h)

/-- `Trace.allocd` is invariant under permutation (it only reads the multiset of
  `alloc` events). -/
theorem Trace.allocd_perm {t t' : Trace} {l : Nat} (h : List.Perm t t') :
    Trace.allocd t l ↔ Trace.allocd t' l := by
  rw [← Trace.mem_allocList, ← Trace.mem_allocList]
  have hp : List.Perm t.allocList t'.allocList := by
    induction h with
    | nil => exact List.Perm.refl _
    | cons x _ ih => cases x <;> simp only [Trace.allocList] <;> first | exact ih | exact ih.cons _
    | swap x y l =>
      cases x <;> cases y <;> simp only [Trace.allocList] <;>
        first | exact List.Perm.refl _ | exact List.Perm.swap _ _ _
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  exact hp.mem_iff

/-- `Trace.touchesWith` is invariant under permutation (order-independent). -/
theorem Trace.touchesWith_perm {t t' : Trace} {l : Nat} {cm : CapMode}
    (h : List.Perm t t') : Trace.touchesWith t l cm ↔ Trace.touchesWith t' l cm := by
  induction h with
  | nil => exact Iff.rfl
  | cons x _ ih => cases x <;> simp only [Trace.touchesWith, ih]
  | swap x y l =>
    cases x <;> cases y <;> simp only [Trace.touchesWith] <;> tauto
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Forward direction of the budget characterisation.**  In a `TraceOk` trace,
  every `touchesWith` event is EITHER covered by the budget, OR targets a location
  the trace allocated.  (Order-independent reading of `TraceOk`.) -/
theorem TraceOkFrom.touchesWith_covered_or_allocd {C : CapabilitySet} {l : Nat}
    {cm : CapMode} :
    ∀ {A : List Nat} {t : Trace}, TraceOkFrom C A t -> Trace.touchesWith t l cm ->
      C.covers cm l ∨ Trace.allocd t l ∨ l ∈ A := by
  intro A t htr
  induction htr with
  | nil => intro h; simp only [Trace.touchesWith] at h
  | @alloc l' A' t' _ ih =>
    intro h
    rcases ih h with hcov | hal | hin
    · exact Or.inl hcov
    · exact Or.inr (Or.inl (by simp only [Trace.allocd]; exact Or.inr hal))
    · rcases List.mem_cons.mp hin with rfl | hin
      · exact Or.inr (Or.inl (by simp [Trace.allocd]))
      · exact Or.inr (Or.inr hin)
  | @access mu l' A' t' hc _ ih =>
    intro h
    rcases h with ⟨hl, hcm⟩ | h
    · subst hl; subst hcm
      rcases hc with hcov | hin
      · exact Or.inl hcov
      · exact Or.inr (Or.inr hin)
    · rcases ih h with hcov | hal | hin
      · exact Or.inl hcov
      · exact Or.inr (Or.inl (by simp only [Trace.allocd]; exact hal))
      · exact Or.inr (Or.inr hin)
  | @dealloc l' A' t' hc _ ih =>
    intro h
    rcases h with ⟨hl, hcm⟩ | h
    · subst hl; subst hcm
      rcases hc with hcov | hin
      · exact Or.inl hcov
      · exact Or.inr (Or.inr hin)
    · rcases ih h with hcov | hal | hin
      · exact Or.inl hcov
      · exact Or.inr (Or.inl (by simp only [Trace.allocd]; exact hal))
      · exact Or.inr (Or.inr hin)

theorem TraceOk.touchesWith_covered_or_allocd {C : CapabilitySet} {l : Nat}
    {cm : CapMode} {t : Trace} (htr : TraceOk t C) (h : Trace.touchesWith t l cm) :
    C.covers cm l ∨ Trace.allocd t l := by
  rcases TraceOkFrom.touchesWith_covered_or_allocd htr h with hcov | hal | hin
  · exact Or.inl hcov
  · exact Or.inr hal
  · simp at hin

/-- **Every location a single `Step` touches is present in the pre-step memory.**
  Each primitive redex looks its target up; the congruence steps recurse. -/
theorem step_touched_present {t : Trace} {m1 e1 m2 e2 : _} {l : Nat}
    (hstep : Step t m1 e1 m2 e2) (htch : Trace.touched t l) : m1.lookup l ≠ none := by
  induction hstep with
  | step_apply | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.touched] at htch
  | step_invoke hlkx _ =>
    simp only [Trace.touched, or_false] at htch; subst htch
    rw [hlkx]; simp
  | step_read _ hlky =>
    simp only [Trace.touched, or_false] at htch; subst htch
    rw [hlky]; simp
  | step_write_true hx _ | step_write_false hx _ =>
    simp only [Trace.touched, or_false] at htch; subst htch
    rw [hx]; simp
  | step_drop hx =>
    simp only [Trace.touched, or_false] at htch; subst htch
    rw [hx]; simp
  | step_alloc _ _ => simp only [Trace.touched] at htch
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ _ _ ih | step_par_right _ _ _ ih => exact ih htch

/-- A cell a step ALLOCATES is fresh in the pre-step memory (only `step_alloc`
  allocates, requiring `m1.heap l = none`). -/
theorem step_allocd_fresh {t : Trace} {m1 e1 m2 e2 : _} {l : Nat}
    (hstep : SeqStep t m1 e1 m2 e2) (hal : Trace.allocd t l) : m1.heap l = none := by
  induction hstep with
  | step_apply | step_invoke _ _ | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write_true _ _ | step_write_false _ _ | step_drop _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.allocd] at hal
  | step_alloc _ hfresh =>
    simp only [Trace.allocd, or_false] at hal; subst hal; exact hfresh
  | step_ctx_letin _ ih | step_ctx_unpack _ ih | step_par_left _ ih => exact ih hal
  | step_par_right _ _ ih => exact ih hal

/-- A cell a step ALLOCATES is present in the post-step memory. -/
theorem step_allocd_present {t : Trace} {m1 e1 m2 e2 : _} {l : Nat}
    (hstep : SeqStep t m1 e1 m2 e2) (hal : Trace.allocd t l) : m2.heap l ≠ none := by
  induction hstep with
  | step_apply | step_invoke _ _ | step_tapply | step_capply | step_unwrap
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_write_true _ _ | step_write_false _ _ | step_drop _
  | step_rename | step_unpack | step_par_join _ _ | step_lift _ _ _ =>
    simp only [Trace.allocd] at hal
  | step_alloc _ hfresh =>
    simp only [Trace.allocd, or_false] at hal; subst hal
    simp [Memory.extend_mcell, Heap.extend_mcell]
  | step_ctx_letin _ ih | step_ctx_unpack _ ih | step_par_left _ ih => exact ih hal
  | step_par_right _ _ ih => exact ih hal

/-- **A step's trace is `TraceOk`-bounded by the stepping expression's budget.**
  Given a full run `hrun` of `e` whose trace `τ` (bounded by `C`) is a permutation
  of `t ++ rest` (`t` = the step's trace), every event in the step's trace `t` is
  bounded by `C`: it is `touchesWith τ`, hence covered by `C` or allocated in `τ`;
  but a step-touched cell is PRESENT in `m` (`step_touched_present`) whereas a
  `τ`-allocated cell is FRESH in `m` (`alloc_fresh`) — so it must be covered. -/
theorem bound_step_trace {t rest τ : Trace} {m m' mf : Memory} {e e' v : Exp {}}
    {C : CapabilitySet}
    (hstep : Step t m e m' e') (hrun : BigStep m e τ v mf)
    (hperm : List.Perm τ (t ++ rest)) (htok : TraceOk τ C) :
    TraceOk t C := by
  have key : ∀ l cm, Trace.touchesWith t l cm -> C.covers cm l := by
    intro l cm htw_t
    have htw_full : Trace.touchesWith (t ++ rest) l cm :=
      Trace.touchesWith_append.mpr (Or.inl htw_t)
    have htw_τ : Trace.touchesWith τ l cm := (Trace.touchesWith_perm hperm).mpr htw_full
    rcases htok.touchesWith_covered_or_allocd htw_τ with hcov | hal
    · exact hcov
    · -- `l` allocated in `τ` ⟹ fresh in `m`; but the step touches `l` ⟹ present.
      exact absurd (hrun.alloc_fresh hal)
        (step_touched_present hstep (Trace.touched_of_touchesWith htw_t))
  -- Now `TraceOkFrom C A t` for any `A` by induction on `t` (allocs need no authority).
  clear hperm htok hrun hstep
  suffices h : ∀ A, TraceOkFrom C A t from h []
  intro A
  induction t generalizing A with
  | nil => exact TraceOkFrom.nil
  | cons it t ih =>
    have key' : ∀ l cm, Trace.touchesWith t l cm -> C.covers cm l := by
      intro l cm h'; refine key l cm ?_
      cases it <;> simp only [Trace.touchesWith] <;> tauto
    cases it with
    | alloc l => exact TraceOkFrom.alloc (ih key' (l :: A))
    | access mu l =>
      refine TraceOkFrom.access (Or.inl (key l (.access mu) ?_)) (ih key' A)
      simp only [Trace.touchesWith]; tauto
    | dealloc l =>
      refine TraceOkFrom.dealloc (Or.inl (key l .drop ?_)) (ih key' A)
      simp only [Trace.touchesWith]; tauto

/-- The "cells added by a run avoid `S`" property composes along a two-stage run. -/
theorem added_avoid_trans {m m1 m' : Memory} {S : Finset Nat}
    (h1 : ∀ c, m1.lookup c ≠ none → m.lookup c = none → c ∉ S)
    (h2 : ∀ c, m'.lookup c ≠ none → m1.lookup c = none → c ∉ S) :
    ∀ c, m'.lookup c ≠ none → m.lookup c = none → c ∉ S := by
  intro c hc' hc
  rcases hm1 : m1.lookup c with _ | cell
  · exact h2 c hc' hm1
  · exact h1 c (by rw [hm1]; exact Option.some_ne_none cell) hc

/-- **Progress with fresh-name avoidance.**  A `Safe` configuration reaches a `BigStep` answer
  whose freshly-allocated cells (every cell present afterwards but absent before) all avoid a
  given finite set `S`.  Same construction as `Safe.has_answer`, but every fresh choice is taken
  outside `S` (`Memory.exists_fresh_avoiding`).  Used to schedule the left branch of a `par` so its
  fresh names are disjoint from the right branch's, letting the right run replay verbatim. -/
theorem Safe.has_answer_avoiding {m : Memory} {e : Exp {}} (h : Safe m e) (S : Finset Nat) :
    ∃ t v m', BigStep m e t v m' ∧
      (∀ c, m'.lookup c ≠ none → m.lookup c = none → c ∉ S) := by
  induction h with
  | ans hans => exact ⟨_, _, _, BigStep.of_isAns hans, fun c hc' hc => absurd hc hc'⟩
  | alloc hlk =>
    obtain ⟨l, hlS, hfresh⟩ := Memory.exists_fresh_avoiding _ S
    refine ⟨_, _, _, BigStep.bs_alloc hlk hfresh, fun c hc' hc => ?_⟩
    obtain ⟨cell, hcc⟩ := Option.ne_none_iff_exists'.mp hc'
    have : c = l := Memory.extend_mcell_lookup_eq_base_of_ne hcc hc
    subst this; exact hlS
  | apply hlk _ ih =>
    obtain ⟨t, v, m', hbs, hadd⟩ := ih
    exact ⟨_, _, _, BigStep.bs_apply hlk hbs, hadd⟩
  | invoke hlk1 hlk2 => exact ⟨_, _, _, BigStep.bs_invoke hlk1 hlk2, fun c hc' hc => absurd hc hc'⟩
  | tapply hlk _ ih =>
    obtain ⟨t, v, m', hbs, hadd⟩ := ih
    exact ⟨_, _, _, BigStep.bs_tapply hlk hbs, hadd⟩
  | capply hlk _ ih =>
    obtain ⟨t, v, m', hbs, hadd⟩ := ih
    exact ⟨_, _, _, BigStep.bs_capply hlk hbs, hadd⟩
  | unwrap hlk _ ih =>
    obtain ⟨t, v, m', hbs, hadd⟩ := ih
    exact ⟨_, _, _, BigStep.bs_unwrap hlk hbs, hadd⟩
  | letin _ h_ans _ _ ih1 ih_val ih_var =>
    obtain ⟨t1, v, m1, hbs1, hadd1⟩ := ih1
    obtain ⟨hsa, hwf1⟩ := h_ans _ _ _ hbs1
    cases hsa with
    | is_simple_val hv =>
      obtain ⟨l', hl'S, hfresh⟩ := Memory.exists_fresh_avoiding m1 S
      obtain ⟨t2, v2, m2, hbs2, hadd2⟩ := ih_val hbs1 hv hwf1 l' hfresh
      refine ⟨_, _, _, BigStep.bs_letin_val hbs1 hv hwf1 hfresh hbs2, ?_⟩
      refine added_avoid_trans (added_avoid_trans hadd1 (fun c hc' hc => ?_)) hadd2
      obtain ⟨cell, hcc⟩ := Option.ne_none_iff_exists'.mp hc'
      by_cases hcl : c = l'
      · subst hcl; exact hl'S
      · rw [Memory.extend_val_lookup_ne hcl] at hcc; rw [hcc] at hc; exact absurd hc (by simp)
    | is_var =>
      obtain ⟨t2, v2, m2, hbs2, hadd2⟩ := ih_var hbs1
      exact ⟨_, _, _, BigStep.bs_letin_var hbs1 hbs2, added_avoid_trans hadd1 hadd2⟩
  | unpack _ h_ans _ ih1 ih_val =>
    obtain ⟨t1, v, m1, hbs1, hadd1⟩ := ih1
    obtain ⟨hpack, hwf1⟩ := h_ans _ _ _ hbs1
    cases hpack with
    | pack =>
      obtain ⟨t2, v2, m2, hbs2, hadd2⟩ := ih_val hbs1
      exact ⟨_, _, _, BigStep.bs_unpack hbs1 hbs2, added_avoid_trans hadd1 hadd2⟩
  | read hlk1 hlk2 =>
    exact ⟨_, _, _, BigStep.bs_read (b' := true) hlk1 hlk2, fun c hc' hc => absurd hc hc'⟩
  | write_true hx hy =>
    refine ⟨_, _, _, BigStep.bs_write_true hx hy, fun c hc' hc => ?_⟩
    rw [Memory.update_mcell_lookup_none hc ⟨_, hx⟩] at hc'; exact absurd rfl hc'
  | write_false hx hy =>
    refine ⟨_, _, _, BigStep.bs_write_false hx hy, fun c hc' hc => ?_⟩
    rw [Memory.update_mcell_lookup_none hc ⟨_, hx⟩] at hc'; exact absurd rfl hc'
  | drop hx =>
    refine ⟨_, _, _, BigStep.bs_drop hx, fun c hc' hc => ?_⟩
    rw [Memory.drop_mcell_lookup_none hc ⟨_, hx⟩] at hc'; exact absurd rfl hc'
  | cond hres _ _ ih_true ih_false =>
    cases hres with
    | inl hbtrue =>
      obtain ⟨t, v, m', hbs, hadd⟩ := ih_true hbtrue
      exact ⟨_, _, _, BigStep.bs_cond_true hbtrue hbs, hadd⟩
    | inr hbfalse =>
      obtain ⟨t, v, m', hbs, hadd⟩ := ih_false hbfalse
      exact ⟨_, _, _, BigStep.bs_cond_false hbfalse hbs, hadd⟩
  | par _ _ _ _ _ _ _ _ _ _ _ _ ih1 _ ih2 _ _ =>
    obtain ⟨t1, v1, m1, hbs1, hadd1⟩ := ih1
    obtain ⟨t2, v2, m2, hbs2, hadd2⟩ := ih2 hbs1
    exact ⟨_, _, _, BigStep.bs_par hbs1 hbs2, added_avoid_trans hadd1 hadd2⟩

/-- A `BigStep` never shrinks the heap domain (`alloc`/`extend` add, `write` mutates in place,
  `drop` leaves a dead mcell). -/
theorem BigStep.lookup_ne_none_mono {m : Memory} {e : Exp {}} {t v m'}
    (hbs : BigStep m e t v m') {c : Nat} (hc : m.lookup c ≠ none) : m'.lookup c ≠ none := by
  obtain ⟨cell, hcell⟩ := Option.ne_none_iff_exists'.mp hc
  obtain ⟨cell', hcell', _⟩ := hbs.subsumes c cell hcell
  rw [show m'.lookup c = m'.heap c from rfl, hcell']; exact Option.some_ne_none cell'

/-- A value cell is reproduced (exactly) in a subsuming memory. -/
theorem Memory.val_up {m ms : Memory} (hsub : ms.subsumes m) {x : Nat} {v : HeapVal}
    (hx : m.lookup x = some (.val v)) : ms.lookup x = some (.val v) := by
  obtain ⟨c', hc', hsubc⟩ := hsub x _ hx
  cases c' with
  | val w => simp only [Cell.subsumes] at hsubc; rw [hsubc] at hc'; exact hc'
  | capability _ => simp [Cell.subsumes] at hsubc
  | masked => simp [Cell.subsumes] at hsubc

/-- A basic capability is reproduced (exactly) in a subsuming memory. -/
theorem Memory.basic_up {m ms : Memory} (hsub : ms.subsumes m) {x : Nat}
    (hx : m.lookup x = some (.capability .basic)) :
    ms.lookup x = some (.capability .basic) := by
  obtain ⟨c', hc', hsubc⟩ := hsub x _ hx
  cases c' with
  | val _ => simp [Cell.subsumes] at hsubc
  | masked => simp [Cell.subsumes] at hsubc
  | capability ci => cases ci with
    | basic => exact hc'
    | mcell _ _ => simp [Cell.subsumes] at hsubc

set_option maxHeartbeats 1000000 in
-- The full induction over `BigStep` with threaded subsumption/liveness/freshness invariants
-- exceeds the default heartbeat budget.
/-- **Same-trace replay in a subsuming super-memory (up transfer).**  A run replays verbatim
  (same trace, same value) from `ms ⊒ m`, provided every mcell the run touches and is live for is
  also live in `ms` (`hrel`, an `IsLive` biconditional at touched cells) and every cell the run
  allocates or leaves behind is fresh in `ms` (`hfresh`).  Names are preserved (no renaming): the
  `letin` reachability divergence is killed by `compute_reachability_monotonic`.  Conclusions
  thread the induction: `ms' ⊒ m'`, the fresh-tracking, and the `simulate_down`-style liveness
  biconditional.  Dual of `BigStep.simulate_down` (which goes down and derives liveness from
  subsumption; up needs `hrel`/`hfresh` because subsumption does not preserve liveness upward). -/
theorem BigStep.transfer {m : Memory} {e : Exp {}} {t v m'} (hbs : BigStep m e t v m') :
    ∀ {ms : Memory}, ms.subsumes m → Exp.WfInHeap e m.heap →
      (hrel : ∀ l, Trace.touched t l → (m.IsLive l ↔ ms.IsLive l)) →
      (hfresh : ∀ c, (Trace.allocd t c ∨ (m'.lookup c ≠ none ∧ m.lookup c = none)) →
        ms.lookup c = none) →
      ∃ ms', BigStep ms e t v ms' ∧ ms'.subsumes m' ∧
        (∀ c, ms.lookup c = none → m'.lookup c = none → ms'.lookup c = none) ∧
        (∀ l, ((m.IsLive l ↔ ms.IsLive l) ∨ Trace.allocd t l) → (m'.IsLive l ↔ ms'.IsLive l)) := by
  induction hbs with
  | bs_pack =>
    intro ms hsub _ _ _
    exact ⟨ms, BigStep.bs_pack, hsub, (fun c hcms _ => hcms),
      fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_val hv =>
    intro ms hsub _ _ _
    exact ⟨ms, BigStep.bs_val hv, hsub, (fun c hcms _ => hcms),
      fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_var =>
    intro ms hsub _ _ _
    exact ⟨ms, BigStep.bs_var, hsub, (fun c hcms _ => hcms),
      fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_wrap =>
    intro ms hsub _ _ _
    exact ⟨ms, BigStep.bs_wrap, hsub, (fun c hcms _ => hcms),
      fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_invoke hlkx hlky =>
    intro ms hsub _ _ _
    exact ⟨ms, BigStep.bs_invoke (Memory.basic_up hsub hlkx) (Memory.val_up hsub hlky), hsub,
      (fun c hcms _ => hcms), fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_read hlkx hlky =>
    intro ms hsub _ hrel _
    obtain ⟨b', hyms⟩ := (hrel _ (by simp [Trace.touched])).mp ⟨_, hlky⟩
    exact ⟨ms, BigStep.bs_read (Memory.val_up hsub hlkx) hyms, hsub,
      (fun c hcms _ => hcms), fun l h => h.resolve_right (by simp [Trace.allocd])⟩
  | bs_alloc hlk hfreshl =>
    intro ms hsub _hwf _hrel hfresh
    rename_i l
    have hlms : ms.heap l = none := hfresh _ (Or.inl (by simp [Trace.allocd]))
    refine ⟨_, BigStep.bs_alloc (Memory.val_up hsub hlk) hlms,
      Memory.extend_mcell_subsumes_compat _ _ hfreshl hlms hsub, ?_, ?_⟩
    · intro c hcms hc'
      have hcl : c ≠ l := fun he => by
        subst he; rw [Memory.extend_mcell_lookup hfreshl] at hc'; cases hc'
      simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hcl]; exact hcms
    · intro lc h
      rcases h with hag | ha
      · exact Memory.extend_mcell_IsLive_agree hag
      · simp only [Trace.allocd, or_false] at ha; subst ha
        exact iff_of_true Memory.extend_mcell_IsLive_self Memory.extend_mcell_IsLive_self
  | bs_apply hlk _ ih =>
    intro ms hsub hwf hrel hfresh
    match hwf with
    | .wf_app (.wf_free _) hwfy =>
      obtain ⟨_, _, he⟩ := Exp.wf_inv_abs (Memory.wf_lookup hlk)
      obtain ⟨ms', hbs', hsub', hft', hrel'⟩ :=
        ih (ms := ms) hsub (Exp.wf_subst he (Subst.wf_openVar hwfy)) hrel hfresh
      exact ⟨ms', BigStep.bs_apply (Memory.val_up hsub hlk) hbs', hsub', hft', hrel'⟩
  | bs_tapply hlk _ ih =>
    intro ms hsub hwf hrel hfresh
    match hwf with
    | .wf_tapp (.wf_free _) _ =>
      obtain ⟨_, _, he⟩ := Exp.wf_inv_tabs (Memory.wf_lookup hlk)
      obtain ⟨ms', hbs', hsub', hft', hrel'⟩ :=
        ih (ms := ms) hsub (Exp.wf_subst he (Subst.wf_openTVar Ty.WfInHeap.wf_top)) hrel hfresh
      exact ⟨ms', BigStep.bs_tapply (Memory.val_up hsub hlk) hbs', hsub', hft', hrel'⟩
  | bs_capply hlk _ ih =>
    intro ms hsub hwf hrel hfresh
    match hwf with
    | .wf_capp (.wf_free _) hcs =>
      obtain ⟨_, _, he⟩ := Exp.wf_inv_cabs (Memory.wf_lookup hlk)
      obtain ⟨ms', hbs', hsub', hft', hrel'⟩ :=
        ih (ms := ms) hsub (Exp.wf_subst he (Subst.wf_openCVar hcs)) hrel hfresh
      exact ⟨ms', BigStep.bs_capply (Memory.val_up hsub hlk) hbs', hsub', hft', hrel'⟩
  | bs_unwrap hlk _ ih =>
    intro ms hsub hwf hrel hfresh
    match hwf with
    | .wf_unwrap (.wf_free _) =>
      obtain ⟨ms', hbs', hsub', hft', hrel'⟩ :=
        ih (ms := ms) hsub (match Memory.wf_lookup hlk with | .wf_boxed _ _ he => he) hrel hfresh
      exact ⟨ms', BigStep.bs_unwrap (Memory.val_up hsub hlk) hbs', hsub', hft', hrel'⟩
  | bs_cond_true hres _ ih =>
    intro ms hsub hwf hrel hfresh
    obtain ⟨_, hwf2, _⟩ := Exp.wf_inv_cond hwf
    obtain ⟨ms', hbs', hsub', hft', hrel'⟩ := ih (ms := ms) hsub hwf2 hrel hfresh
    exact ⟨ms', BigStep.bs_cond_true (resolve_monotonic hsub hres) hbs', hsub', hft', hrel'⟩
  | bs_cond_false hres _ ih =>
    intro ms hsub hwf hrel hfresh
    obtain ⟨_, _, hwf3⟩ := Exp.wf_inv_cond hwf
    obtain ⟨ms', hbs', hsub', hft', hrel'⟩ := ih (ms := ms) hsub hwf3 hrel hfresh
    exact ⟨ms', BigStep.bs_cond_false (resolve_monotonic hsub hres) hbs', hsub', hft', hrel'⟩
  | bs_write_true hx hy =>
    intro ms hsub _ hrel _
    obtain ⟨_, hxms⟩ := (hrel _ (by simp [Trace.touched])).mp ⟨_, hx⟩
    refine ⟨_, BigStep.bs_write_true hxms (Memory.val_up hsub hy),
      Memory.update_mcell_subsumes_compat _ _ _ ⟨_, hx⟩ ⟨_, hxms⟩ hsub,
      (fun c hcms _ => Memory.update_mcell_lookup_none hcms ⟨_, hxms⟩), ?_⟩
    intro lc h
    exact Memory.update_mcell_IsLive_agree (h.resolve_right (by simp [Trace.allocd]))
  | bs_write_false hx hy =>
    intro ms hsub _ hrel _
    obtain ⟨_, hxms⟩ := (hrel _ (by simp [Trace.touched])).mp ⟨_, hx⟩
    refine ⟨_, BigStep.bs_write_false hxms (Memory.val_up hsub hy),
      Memory.update_mcell_subsumes_compat _ _ _ ⟨_, hx⟩ ⟨_, hxms⟩ hsub,
      (fun c hcms _ => Memory.update_mcell_lookup_none hcms ⟨_, hxms⟩), ?_⟩
    intro lc h
    exact Memory.update_mcell_IsLive_agree (h.resolve_right (by simp [Trace.allocd]))
  | bs_drop hx =>
    intro ms hsub _ hrel _
    obtain ⟨_, hxms⟩ := (hrel _ (by simp [Trace.touched])).mp ⟨_, hx⟩
    refine ⟨_, BigStep.bs_drop hxms,
      Memory.drop_mcell_subsumes_compat _ ⟨_, hx⟩ ⟨_, hxms⟩ hsub,
      (fun c hcms _ => Memory.drop_mcell_lookup_none hcms ⟨_, hxms⟩), ?_⟩
    intro lc h
    exact Memory.drop_mcell_IsLive_agree (h.resolve_right (by simp [Trace.allocd]))
  | bs_letin_val hbs1 hv hwf1 hfreshl hbs2 ih1 ih2 =>
    intro ms hsub hwf hrel hfresh
    rename_i th tk vf ekb m0 mh mfin vh ln
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    have hfresh_h : ∀ c, (Trace.allocd th c ∨ (mh.lookup c ≠ none ∧ m0.lookup c = none)) →
        ms.lookup c = none := by
      intro c h
      rcases h with ha | ⟨h1, h0⟩
      · exact hfresh c (Or.inl (Trace.allocd_append.mpr (Or.inl ha)))
      · have hcl : c ≠ ln := fun he => by subst he; exact h1 hfreshl
        exact hfresh c (Or.inr
          ⟨hbs2.lookup_ne_none_mono (by rw [Memory.extend_val_lookup_ne hcl]; exact h1), h0⟩)
    obtain ⟨msh, hbs_h', hsubh, hFTh, hrelh⟩ := ih1 (ms := ms) hsub hwf_e1
      (fun l hl => hrel l (Trace.touched_append.mpr (Or.inl hl))) hfresh_h
    have hm_ln : m0.lookup ln = none := by
      by_contra h; exact (hbs1.lookup_ne_none_mono h) hfreshl
    have hmfin_ln : mfin.lookup ln ≠ none :=
      hbs2.lookup_ne_none_mono (by rw [Memory.extend_val_lookup_self]; exact Option.some_ne_none _)
    have hl'msh : msh.lookup ln = none := hFTh ln (hfresh ln (Or.inr ⟨hmfin_ln, hm_ln⟩)) hfreshl
    have hReq : compute_reachability msh.heap vh hv = compute_reachability mh.heap vh hv :=
      compute_reachability_monotonic hsubh vh hv hwf1
    have hwf_v_msh : Exp.WfInHeap vh msh.heap := Exp.wf_monotonic hsubh hwf1
    have hwf_body : Exp.WfInHeap (ekb.subst (Subst.openVar (.free ln)))
        (mh.extend_val ln ⟨vh, hv, compute_reachability mh.heap vh hv⟩ hwf1 rfl hfreshl).heap :=
      Exp.wf_subst (Exp.wf_monotonic
        (Heap.subsumes_trans (Heap.extend_subsumes hfreshl) (BigStep.subsumes hbs1)) hwf_e2)
        (Subst.wf_openVar (Var.WfInHeap.wf_free (Heap.extend_lookup_eq _ _ _)))
    have hsub_k : (msh.extend_val ln ⟨vh, hv, compute_reachability msh.heap vh hv⟩ hwf_v_msh rfl
        hl'msh).subsumes (mh.extend_val ln ⟨vh, hv, compute_reachability mh.heap vh hv⟩ hwf1 rfl
        hfreshl) :=
      Memory.extend_val_subsumes_compat (by rw [hReq]) hwf1 rfl hfreshl hwf_v_msh rfl hl'msh hsubh
    have hrel_k : ∀ lc, Trace.touched tk lc →
        ((mh.extend_val ln ⟨vh, hv, compute_reachability mh.heap vh hv⟩ hwf1 rfl hfreshl).IsLive lc
          ↔ (msh.extend_val ln ⟨vh, hv, compute_reachability msh.heap vh hv⟩ hwf_v_msh rfl
            hl'msh).IsLive lc) := by
      intro lc hlc
      by_cases hcl : lc = ln
      · subst hcl
        exact iff_of_false Memory.extend_val_not_IsLive_self Memory.extend_val_not_IsLive_self
      · rw [Memory.extend_val_IsLive_ne hcl, Memory.extend_val_IsLive_ne hcl]
        exact hrelh lc (Or.inl (hrel lc (Trace.touched_append.mpr (Or.inr hlc))))
    have hfresh_k : ∀ c, (Trace.allocd tk c ∨ (mfin.lookup c ≠ none ∧
          (mh.extend_val ln ⟨vh, hv, compute_reachability mh.heap vh hv⟩ hwf1 rfl hfreshl).lookup c
            = none)) →
        (msh.extend_val ln ⟨vh, hv, compute_reachability msh.heap vh hv⟩ hwf_v_msh rfl
          hl'msh).lookup c = none := by
      intro c h
      rcases h with ha | ⟨h1, h0⟩
      · have hext0 := hbs2.alloc_fresh ha
        have hcl : c ≠ ln := fun he => by
          subst he; rw [Memory.extend_val_lookup_self] at hext0; cases hext0
        have hmhc : mh.lookup c = none := by
          rw [Memory.extend_val_lookup_ne hcl] at hext0; exact hext0
        rw [Memory.extend_val_lookup_ne hcl]
        exact hFTh c (hfresh c (Or.inl (Trace.allocd_append.mpr (Or.inr ha)))) hmhc
      · have hcl : c ≠ ln := fun he => by
          subst he; rw [Memory.extend_val_lookup_self] at h0; cases h0
        have hmhc : mh.lookup c = none := by rw [Memory.extend_val_lookup_ne hcl] at h0; exact h0
        have hm0c : m0.lookup c = none := by
          by_contra hh; exact (hbs1.lookup_ne_none_mono hh) hmhc
        rw [Memory.extend_val_lookup_ne hcl]
        exact hFTh c (hfresh c (Or.inr ⟨h1, hm0c⟩)) hmhc
    obtain ⟨msf, hbs_k', hsubf, hFTf, hrelf⟩ := ih2 (ms := msh.extend_val ln
        ⟨vh, hv, compute_reachability msh.heap vh hv⟩ hwf_v_msh rfl hl'msh) hsub_k hwf_body
      hrel_k hfresh_k
    refine ⟨msf, BigStep.bs_letin_val hbs_h' hv hwf_v_msh hl'msh hbs_k', hsubf, ?_, ?_⟩
    · intro c hcms hcmf
      have hmhext : (mh.extend_val ln ⟨vh, hv, compute_reachability mh.heap vh hv⟩ hwf1 rfl
          hfreshl).lookup c = none := by by_contra h; exact (hbs2.lookup_ne_none_mono h) hcmf
      have hcl : c ≠ ln := fun he => by
        subst he; rw [Memory.extend_val_lookup_self] at hmhext; cases hmhext
      have hmhc : mh.lookup c = none := by
        rw [Memory.extend_val_lookup_ne hcl] at hmhext; exact hmhext
      exact hFTf c (by rw [Memory.extend_val_lookup_ne hcl]; exact hFTh c hcms hmhc) hcmf
    · intro lc h
      apply hrelf
      by_cases hcl : lc = ln
      · subst hcl
        exact Or.inl (iff_of_false Memory.extend_val_not_IsLive_self
          Memory.extend_val_not_IsLive_self)
      · rw [Memory.extend_val_IsLive_ne hcl, Memory.extend_val_IsLive_ne hcl]
        rcases h with hag | ha
        · exact Or.inl (hrelh lc (Or.inl hag))
        · rcases Trace.allocd_append.mp ha with h1 | h2
          · exact Or.inl (hrelh lc (Or.inr h1))
          · exact Or.inr h2
  | bs_letin_var hbs1 hbs2 ih1 ih2 =>
    intro ms hsub hwf hrel hfresh
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    obtain ⟨msh, hbs_h', hsubh, hFTh, hrelh⟩ := ih1 (ms := ms) hsub hwf_e1
      (fun l hl => hrel l (Trace.touched_append.mpr (Or.inl hl)))
      (fun c h => h.elim (fun ha => hfresh c (Or.inl (Trace.allocd_append.mpr (Or.inl ha))))
        (fun ⟨h1, h0⟩ => hfresh c (Or.inr ⟨hbs2.lookup_ne_none_mono h1, h0⟩)))
    have hwf_body := Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes hbs1) hwf_e2)
      (match BigStep.wf_answer hbs1 hwf_e1 with | Exp.WfInHeap.wf_var hx => Subst.wf_openVar hx)
    obtain ⟨msf, hbs_k', hsubf, hFTf, hrelf⟩ := ih2 (ms := msh) hsubh hwf_body
      (fun lc hlc => hrelh lc (Or.inl (hrel lc (Trace.touched_append.mpr (Or.inr hlc)))))
      (fun c h => h.elim
        (fun ha => hFTh c (hfresh c (Or.inl (Trace.allocd_append.mpr (Or.inr ha))))
          (hbs2.alloc_fresh ha))
        (fun ⟨h1, h0⟩ => hFTh c (hfresh c (Or.inr ⟨h1, by
          by_contra hh; exact (hbs1.lookup_ne_none_mono hh) h0⟩)) h0))
    refine ⟨msf, BigStep.bs_letin_var hbs_h' hbs_k', hsubf,
      (fun c hcms hcmf => hFTf c (hFTh c hcms
        (by by_contra hh; exact (hbs2.lookup_ne_none_mono hh) hcmf)) hcmf), ?_⟩
    intro lc h
    apply hrelf
    rcases h with hag | ha
    · exact Or.inl (hrelh lc (Or.inl hag))
    · rcases Trace.allocd_append.mp ha with h1 | h2
      · exact Or.inl (hrelh lc (Or.inr h1))
      · exact Or.inr h2
  | bs_unpack hbs1 hbs2 ih1 ih2 =>
    intro ms hsub hwf hrel hfresh
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_unpack hwf
    obtain ⟨msh, hbs_h', hsubh, hFTh, hrelh⟩ := ih1 (ms := ms) hsub hwf_e1
      (fun l hl => hrel l (Trace.touched_append.mpr (Or.inl hl)))
      (fun c h => h.elim (fun ha => hfresh c (Or.inl (Trace.allocd_append.mpr (Or.inl ha))))
        (fun ⟨h1, h0⟩ => hfresh c (Or.inr ⟨hbs2.lookup_ne_none_mono h1, h0⟩)))
    have hwf_body := Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes hbs1) hwf_e2)
      (match BigStep.wf_answer hbs1 hwf_e1 with
        | Exp.WfInHeap.wf_pack hcs hx => Subst.wf_unpack hcs hx)
    obtain ⟨msf, hbs_k', hsubf, hFTf, hrelf⟩ := ih2 (ms := msh) hsubh hwf_body
      (fun lc hlc => hrelh lc (Or.inl (hrel lc (Trace.touched_append.mpr (Or.inr hlc)))))
      (fun c h => h.elim
        (fun ha => hFTh c (hfresh c (Or.inl (Trace.allocd_append.mpr (Or.inr ha))))
          (hbs2.alloc_fresh ha))
        (fun ⟨h1, h0⟩ => hFTh c (hfresh c (Or.inr ⟨h1, by
          by_contra hh; exact (hbs1.lookup_ne_none_mono hh) h0⟩)) h0))
    refine ⟨msf, BigStep.bs_unpack hbs_h' hbs_k', hsubf,
      (fun c hcms hcmf => hFTf c (hFTh c hcms
        (by by_contra hh; exact (hbs2.lookup_ne_none_mono hh) hcmf)) hcmf), ?_⟩
    intro lc h
    apply hrelf
    rcases h with hag | ha
    · exact Or.inl (hrelh lc (Or.inl hag))
    · rcases Trace.allocd_append.mp ha with h1 | h2
      · exact Or.inl (hrelh lc (Or.inr h1))
      · exact Or.inr h2
  | bs_par hbs1 hbs2 ih1 ih2 =>
    intro ms hsub hwf hrel hfresh
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_par hwf
    obtain ⟨msh, hbs_h', hsubh, hFTh, hrelh⟩ := ih1 (ms := ms) hsub hwf_e1
      (fun l hl => hrel l (Trace.touched_append.mpr (Or.inl hl)))
      (fun c h => h.elim (fun ha => hfresh c (Or.inl (Trace.allocd_append.mpr (Or.inl ha))))
        (fun ⟨h1, h0⟩ => hfresh c (Or.inr ⟨hbs2.lookup_ne_none_mono h1, h0⟩)))
    obtain ⟨msf, hbs_k', hsubf, hFTf, hrelf⟩ :=
      ih2 (ms := msh) hsubh (Exp.wf_monotonic (BigStep.subsumes hbs1) hwf_e2)
      (fun lc hlc => hrelh lc (Or.inl (hrel lc (Trace.touched_append.mpr (Or.inr hlc)))))
      (fun c h => h.elim
        (fun ha => hFTh c (hfresh c (Or.inl (Trace.allocd_append.mpr (Or.inr ha))))
          (hbs2.alloc_fresh ha))
        (fun ⟨h1, h0⟩ => hFTh c (hfresh c (Or.inr ⟨h1, by
          by_contra hh; exact (hbs1.lookup_ne_none_mono hh) h0⟩)) h0))
    refine ⟨msf, BigStep.bs_par hbs_h' hbs_k', hsubf,
      (fun c hcms hcmf => hFTf c (hFTh c hcms
        (by by_contra hh; exact (hbs2.lookup_ne_none_mono hh) hcmf)) hcmf), ?_⟩
    intro lc h
    apply hrelf
    rcases h with hag | ha
    · exact Or.inl (hrelh lc (Or.inl hag))
    · rcases Trace.allocd_append.mp ha with h1 | h2
      · exact Or.inl (hrelh lc (Or.inr h1))
      · exact Or.inr h2

/-- Writing an mcell (keeping it live) preserves the liveness of every cell `l`. -/
theorem Memory.update_mcell_preserves_live {m : Memory} (x : Nat) {b : Bool} {h} {l : Nat}
    (hl : m.IsLive l) : (m.update_mcell x b .live h).IsLive l := by
  by_cases hlx : l = x
  · subst hlx; exact Memory.update_mcell_IsLive_self
  · exact (Memory.update_mcell_IsLive_ne hlx).mpr hl

/-- A `BigStep` keeps every live cell live unless its trace externally drops it. -/
theorem BigStep.frameLive {m : Memory} {e : Exp {}} {t v m'}
    (hbs : BigStep m e t v m') : Memory.FrameLive m t m' := by
  induction hbs with
  | bs_pack | bs_val _ | bs_var | bs_wrap | bs_invoke _ _ | bs_read _ _ =>
    exact Memory.FrameLive.refl
  | bs_apply _ _ ih | bs_tapply _ _ ih | bs_capply _ _ ih | bs_unwrap _ _ ih
  | bs_cond_true _ _ ih | bs_cond_false _ _ ih =>
    exact ih
  | bs_par hbs1 hbs2 ih1 ih2 =>
    exact Memory.FrameLive.append ih1 ih2 (fun l b hlive ha =>
      absurd (BigStep.alloc_fresh hbs1 ha) (by rw [hlive]; simp))
  | bs_alloc hlk hfr =>
    intro l b hlive _
    refine (Memory.extend_mcell_IsLive_ne ?_).mpr ⟨b, hlive⟩
    rintro rfl; exact absurd hlive (by simp [Memory.lookup, hfr])
  | bs_write_true hx hy | bs_write_false hx hy =>
    intro l b hlive _
    exact Memory.update_mcell_preserves_live _ ⟨b, hlive⟩
  | bs_drop hx =>
    intro l b hlive hnd
    refine (Memory.drop_mcell_IsLive_ne ?_).mpr ⟨b, hlive⟩
    rintro rfl; exact hnd (by simp [Trace.extDrops, Trace.extDropsFrom])
  | bs_letin_val hrun_e1 hv hwf_v hfr hrun_e2 ih1 ih2 =>
    refine Memory.FrameLive.append ih1 ?_ (fun l b hlive ha =>
      absurd (BigStep.alloc_fresh hrun_e1 ha) (by rw [hlive]; simp))
    intro l b hlive hnd
    refine ih2 l b ((Memory.extend_val_lookup_ne ?_).trans hlive) hnd
    rintro rfl; exact absurd hlive (by simp [hfr])
  | bs_letin_var hrun_e1 hrun_e2 ih1 ih2 =>
    exact Memory.FrameLive.append ih1 ih2 (fun l b hlive ha =>
      absurd (BigStep.alloc_fresh hrun_e1 ha) (by rw [hlive]; simp))
  | bs_unpack hrun_e1 hrun_e2 ih1 ih2 =>
    exact Memory.FrameLive.append ih1 ih2 (fun l b hlive ha =>
      absurd (BigStep.alloc_fresh hrun_e1 ha) (by rw [hlive]; simp))

/-- **Separated budgets do not drop each other's cells.**  If a trace `t` is `TraceOk` for `B2`
  and `B1`/`B2` are non-interfering, then no cell of `B1` is externally dropped by `t`: a drop
  would force the covering `B2` member to `.access .ro` (`shared_ro`), contradicting `.drop`. -/
theorem not_extDrops_of_noninterf {B1 B2 : CapabilitySet} {t : Trace} {l : Nat} {mu1 : CapMode}
    (htok : TraceOk t B2) (hni : CapabilitySet.Noninterference B1 B2)
    (hmem : B1.hasmem mu1 l) : ¬ Trace.extDrops t l := by
  intro hd
  obtain ⟨mu2, hmem2, hle⟩ :=
    CapabilitySet.covers_imp_exists_hasmem (htok.drop_covers_of_extDrops hd)
  obtain ⟨_, hro2⟩ := hni.shared_ro hmem hmem2
  subst hro2
  cases hle

set_option maxHeartbeats 1000000 in
-- The multi-stage construction (avoiding run + verbatim transfer) exceeds the default budget.
/-- **Right-branch liveness frame for `Safe.lift`'s `par` case.**  When lifting
  `Safe m1 (.par Cs1 Cs2 e1 e2)` to `m2 ⊒ m1`, the new unconditional right field `Safe m2 e2` is
  produced by lifting `Safe m1 e2` with the per-run frame `hok_e2 : extTouches t l → l live in m2`.
  Discharged without any renaming/equivariance: schedule the left branch's answer run to avoid
  `e2`'s fresh names (`Safe.has_answer_avoiding` over `dom(mf) ∪ allocList t`, a superset of `e2`'s
  fresh cells), so `e2` replays verbatim from the post-`e1` memory `ms` (`BigStep.transfer`: names
  preserved, mcell liveness off the noninterference frame `hb1`/`hb2`/`hni`, reachability via
  `compute_reachability_monotonic`).  The replayed run touches the same `l`, so the par run
  `e1`-then-`e2`-from-`ms` touches `l`, and the par's frame `hok` keeps `l` live in `m2`. -/
theorem BigStep.par_right_keepsLive
    {m1 m2 mf : Memory} {e1 e2 : Exp {}} {Cs1 Cs2 : CaptureSet {}}
    {C1 C2 : CapabilitySet} {t : Trace} {v2 : Exp {}} {l : Nat} {b : Bool}
    (hs1 : Safe m1 e1) (hbs2 : BigStep m1 e2 t v2 mf)
    (hwf_e1 : Exp.WfInHeap e1 m1.heap) (hwf_e2 : Exp.WfInHeap e2 m1.heap)
    (hb1 : ∀ {m' : Memory} {s : Trace} {v : Exp {}} {m''},
      m'.subsumes m1 → Exp.WfInHeap e1 m'.heap → BigStep m' e1 s v m'' → TraceOk s C1)
    (hb2 : ∀ {m' : Memory} {s : Trace} {v : Exp {}} {m''},
      m'.subsumes m1 → Exp.WfInHeap e2 m'.heap → BigStep m' e2 s v m'' → TraceOk s C2)
    (hni : CapabilitySet.Noninterference C1 C2)
    (hpres2 : ∀ mu c, C2.hasmem mu c → m1.heap c ≠ none)
    (hok : ∀ tt vv mm, mm.subsumes m1 ->
        BigStep m1 (.par Cs1 Cs2 e1 e2) tt vv mm -> Memory.SubsumeOk m1 tt m2)
    (hl_live : m1.lookup l = some (.capability (.mcell b .live)))
    (htouch : Trace.extTouches t l) :
    ∃ b', m2.lookup l = some (.capability (.mcell b' .live)) := by
  -- `S` overapproximates `e2`'s fresh names; schedule `e1` to avoid them.
  obtain ⟨dommf, hdommf⟩ := mf.findom
  obtain ⟨s1, v1, ms, hbs1, hadd1⟩ := hs1.has_answer_avoiding (dommf ∪ (Trace.allocList t).toFinset)
  have htok1 : TraceOk s1 C1 := hb1 (Memory.subsumes_refl _) hwf_e1 hbs1
  have htok2 : TraceOk t C2 := hb2 (Memory.subsumes_refl _) hwf_e2 hbs2
  have hsub : ms.subsumes m1 := BigStep.subsumes hbs1
  have hmemS : ∀ c, Trace.allocd t c → c ∈ dommf ∪ (Trace.allocList t).toFinset := fun c ha =>
    Finset.mem_union.mpr (Or.inr (List.mem_toFinset.mpr (Trace.mem_allocList.mpr ha)))
  -- liveness biconditional at touched cells: `e1` is `C1`-only, disjoint from `C2`'s touched cells.
  have hrel : ∀ c, Trace.touched t c → (m1.IsLive c ↔ ms.IsLive c) := by
    intro c hc
    by_cases hcm1 : m1.lookup c = none
    · constructor
      · rintro ⟨bb, hbb⟩; rw [hcm1] at hbb; cases hbb
      · rintro ⟨bb, hbb⟩
        have hal : Trace.allocd t c := by
          by_contra hnal
          obtain ⟨cm, hext⟩ :=
            Trace.extTouchesMode_of_touched hnal hc
          obtain ⟨mu, hmem, _⟩ :=
            CapabilitySet.covers_imp_exists_hasmem (htok2.covers_of_extTouchesMode hext)
          exact hpres2 mu c hmem hcm1
        exact absurd (hadd1 c (Option.ne_none_iff_exists'.mpr ⟨_, hbb⟩) hcm1) (by
          simp only [not_not]; exact hmemS c hal)
    · have hnal : ¬ Trace.allocd t c := fun ha => hcm1 (BigStep.alloc_fresh hbs2 ha)
      obtain ⟨cm, hext⟩ := Trace.extTouchesMode_of_touched hnal hc
      obtain ⟨mu, hmem, _⟩ :=
        CapabilitySet.covers_imp_exists_hasmem (htok2.covers_of_extTouchesMode hext)
      obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.mp hcm1
      constructor
      · rintro ⟨bb, hbb⟩
        exact BigStep.frameLive hbs1 c bb hbb
          (not_extDrops_of_noninterf htok1 (CapabilitySet.Noninterference.ni_symm hni) hmem)
      · rintro ⟨bb, hbb⟩
        exact Memory.mcell_lookup_down hsub hc0 hbb
  have hfresh : ∀ c, (Trace.allocd t c ∨ (mf.lookup c ≠ none ∧ m1.lookup c = none)) →
      ms.lookup c = none := by
    intro c h
    by_contra hne
    rcases h with ha | ⟨h1, h0⟩
    · exact hadd1 c hne (BigStep.alloc_fresh hbs2 ha) (hmemS c ha)
    · exact hadd1 c hne h0 (Finset.mem_union.mpr (Or.inl ((hdommf c).mp h1)))
  obtain ⟨ms', hbs2_ms, _, _, _⟩ := hbs2.transfer hsub hwf_e2 hrel hfresh
  -- `l` is pre-existing in `m1`, so `e1`'s run does not freshly allocate it.
  have hnal_s1 : ¬ Trace.allocd s1 l := fun ha => by
    have hnone := BigStep.alloc_fresh hbs1 ha; rw [hnone] at hl_live; cases hl_live
  have htouchF : Trace.extTouches (s1 ++ t) l :=
    Trace.extTouchesFrom_append_right hnal_s1 (by simp) htouch
  have hfull := BigStep.bs_par (C1 := Cs1) (C2 := Cs2) hbs1 hbs2_ms
  exact hok _ _ _ hfull.subsumes hfull l b hl_live htouchF

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
      (hpres _ _ _ (BigStep.bs_read (b' := true) hlkx hlky))
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
  | par hs1 hs2 h2 hb1 hb2 hrs1 hrs2 hpres1 hpres2 hcov1 hcov2 hni ih1 ihb ih2 _ih_hrs1 _ih_hrs2 =>
    clear m1
    rename_i e1 e2 m1 _ _ Cs1 Cs2
    cases hwf with
    | wf_par hwf_C1 hwf_C2 hwf_e1 hwf_e2 =>
      -- Budgets `C1`/`C2` are unchanged by lifting; bounds/safety/NI transport by `subsumes_trans`,
      -- presence by `none_of_subsumes_none`, the `hcov` link by `reachability_monotonic`.
      have hok_e1 : ∀ t v m, m.subsumes m1 -> BigStep m1 e1 t v m ->
          Memory.SubsumeOk m1 t m2 := by
        intro t v m _ hbs1
        obtain ⟨t2, v2, mf, hbs2⟩ := (h2 hbs1).has_answer
        have hfull := BigStep.bs_par (C1 := Cs1) (C2 := Cs2) hbs1 hbs2
        exact (hok _ _ _ hfull.subsumes (hpres _ _ _ hfull)).mono_append
      -- Right field `Safe m2 e2`: lift `Safe m1 e2` with a per-run frame discharged by
      -- `BigStep.par_right_keepsLive`.
      have hok_e2 : ∀ t v m, m.subsumes m1 -> BigStep m1 e2 t v m ->
          Memory.SubsumeOk m1 t m2 := by
        intro t v m _ hbs2 l b hl_live htouch
        exact BigStep.par_right_keepsLive hs1 hbs2 hwf_e1 hwf_e2 hb1 hb2 hni hpres2
          (fun tt vv mm hsm hbs => hok tt vv mm hsm (hpres tt vv mm hbs)) hl_live htouch
      refine Safe.par
        (ih1 (Q := fun t v m => BigStep m1 e1 t v m) hsub (fun _ _ _ h => h) hok_e1 hwf_e1)
        (ihb (Q := fun t v m => BigStep m1 e2 t v m) hsub (fun _ _ _ h => h) hok_e2 hwf_e2)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hni
      · intro t1 v1 m1' hbs_m2
        obtain ⟨m_sim, hbs_m1, hsub_sim, hlive⟩ := hbs_m2.simulate_down hsub hwf_e1
        refine ih2 hbs_m1 hsub_sim (fun _ _ _ h => h) ?_
          (Exp.wf_monotonic (BigStep.subsumes hbs_m1) hwf_e2)
        intro t2 vc mc _ hbs_cont l bl hlk_l htouch
        by_cases hal : Trace.allocd t1 l
        · exact (hlive l (Or.inr hal)).mp ⟨bl, hlk_l⟩
        · rcases hm1 : m1.lookup l with _ | c
          · exact absurd (BigStep.live_appears_allocd hbs_m1 hm1 hlk_l) hal
          · obtain ⟨b1, hm1_live⟩ := Memory.mcell_lookup_down hbs_m1.subsumes hm1 hlk_l
            have htouchF : Trace.extTouches (t1 ++ t2) l :=
              Trace.extTouchesFrom_append_right hal (by simp) htouch
            have hfull := BigStep.bs_par (C1 := Cs1) (C2 := Cs2) hbs_m1 hbs_cont
            obtain ⟨b2, hm2_live⟩ :=
              hok _ _ _ hfull.subsumes (hpres _ _ _ hfull) l b1 hm1_live htouchF
            exact (hlive l (Or.inl (iff_of_true ⟨b1, hm1_live⟩ ⟨b2, hm2_live⟩))).mp ⟨bl, hlk_l⟩
      · -- Lifted bound `hb1`: a bound over `m' ⊒ m1` is a fortiori over `m' ⊒ m2`.
        intro m' t v m'' hsub' hwf' hbs
        exact hb1 (Memory.subsumes_trans hsub' hsub) hwf' hbs
      · intro m' t v m'' hsub' hwf' hbs
        exact hb2 (Memory.subsumes_trans hsub' hsub) hwf' hbs
      · -- Lifted robust left-branch safety: monotone in the base memory.
        intro m' hsub' hcompat
        exact hrs1 (Memory.subsumes_trans hsub' hsub) hcompat
      · -- Lifted robust right-branch safety: monotone in the base memory.
        intro m' hsub' hcompat
        exact hrs2 (Memory.subsumes_trans hsub' hsub) hcompat
      · -- Budget presence is preserved upward (subsumption keeps cells present).
        intro mu l hmem hcontra
        exact hpres1 mu l hmem (Heap.none_of_subsumes_none hsub hcontra)
      · intro mu l hmem hcontra
        exact hpres2 mu l hmem (Heap.none_of_subsumes_none hsub hcontra)
      · -- Link transported by `reachability_monotonic` (annotation reachability frozen).
        rw [CaptureSet.reachability_monotonic hsub _ hwf_C1]; exact hcov1
      · rw [CaptureSet.reachability_monotonic hsub _ hwf_C2]; exact hcov2
  | letin _ h_ans h_val h_var ih1 ih_val ih_var =>
    clear m1
    rename_i e1 e2 m1 _
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_letin hwf
    -- `hok` for `e1`: run the continuation to a `letin`-answer, apply the outer `hok` to the
    -- full run, and restrict the footprint back to `t` via `mono_append`.
    have hok_e1 : ∀ t v m, m.subsumes m1 -> BigStep m1 e1 t v m ->
        Memory.SubsumeOk m1 t m2 := by
      intro t v m _ hbs1
      obtain ⟨hsa, hwf_v⟩ := h_ans _ _ _ hbs1
      cases hsa with
      | is_simple_val hv =>
        obtain ⟨lf, hfreshf⟩ := Memory.exists_fresh m
        obtain ⟨t2, v2, mf, hbs2⟩ := (h_val hbs1 hv hwf_v lf hfreshf).has_answer
        have hfull := BigStep.bs_letin_val hbs1 hv hwf_v hfreshf hbs2
        exact (hok _ _ _ hfull.subsumes (hpres _ _ _ hfull)).mono_append
      | is_var =>
        obtain ⟨t2, v2, mf, hbs2⟩ := (h_var hbs1).has_answer
        have hfull := BigStep.bs_letin_var hbs1 hbs2
        exact (hok _ _ _ hfull.subsumes (hpres _ _ _ hfull)).mono_append
    refine Safe.letin
      (ih1 (Q := fun t v m => BigStep m1 e1 t v m) hsub (fun _ _ _ h => h) hok_e1 hwf_e1)
      ?_ ?_ ?_
    · -- `h_ans` lifts: the simulated `m1`-run gives the same (simple) answer value.
      intro t1 v m1' hbs_m2
      obtain ⟨m_sim, hbs_m1, _, _⟩ := hbs_m2.simulate_down hsub hwf_e1
      exact ⟨(h_ans _ _ _ hbs_m1).1, BigStep.wf_answer hbs_m2 (Exp.wf_monotonic hsub hwf_e1)⟩
    · -- `h_val` lifts: replay `e1` from `m1` (simulate), apply the `m1`-side `h_val`,
      -- then lift the continuation through `ih_val` with a frame `hok`.
      intro t1 m1' v hbs_m2 hv hwf_v lf hfresh
      obtain ⟨m_sim, hbs_m1, hsub_sim, hlive⟩ := hbs_m2.simulate_down hsub hwf_e1
      have hwf_v_sim : Exp.WfInHeap v m_sim.heap := BigStep.wf_answer hbs_m1 hwf_e1
      have hfresh_sim : m_sim.lookup lf = none := Heap.none_of_subsumes_none hsub_sim hfresh
      refine ih_val hbs_m1 hv hwf_v_sim lf hfresh_sim
        (m2 := m1'.extend_val lf ⟨v, hv, compute_reachability m1'.heap v hv⟩ hwf_v rfl hfresh)
        (Memory.extend_val_subsumes_compat
          (by rw [compute_reachability_monotonic hsub_sim _ hv hwf_v_sim])
          hwf_v_sim rfl hfresh_sim hwf_v rfl hfresh hsub_sim)
        (fun _ _ _ h => h) ?_
        (Exp.wf_subst
          (Exp.wf_monotonic
            (Heap.subsumes_trans (Heap.extend_subsumes hfresh_sim) (BigStep.subsumes hbs_m1))
            hwf_e2)
          (Subst.wf_openVar (Var.WfInHeap.wf_free (Heap.extend_lookup_eq _ _ _))))
      -- frame `hok` for the continuation: a cell live at the extended `m_sim` and
      -- touched by `t2` is live at the extended `m1'`.
      intro t2 vc mc _ hbs_cont l bl hlk_l htouch
      by_cases hll' : l = lf
      · subst hll'; exact absurd ⟨bl, hlk_l⟩ Memory.extend_val_not_IsLive_self
      · obtain ⟨bs, hbs_sim⟩ := (Memory.extend_val_IsLive_ne hll').mp ⟨bl, hlk_l⟩
        refine (Memory.extend_val_IsLive_ne hll').mpr ?_
        by_cases hal : Trace.allocd t1 l
        · exact (hlive l (Or.inr hal)).mp ⟨bs, hbs_sim⟩
        · rcases hm1 : m1.lookup l with _ | c
          · exact absurd (BigStep.live_appears_allocd hbs_m1 hm1 hbs_sim) hal
          · obtain ⟨b1, hm1_live⟩ := Memory.mcell_lookup_down hbs_m1.subsumes hm1 hbs_sim
            have htouchF : Trace.extTouches (t1 ++ t2) l :=
              Trace.extTouchesFrom_append_right hal (by simp) htouch
            have hfull := BigStep.bs_letin_val hbs_m1 hv hwf_v_sim hfresh_sim hbs_cont
            obtain ⟨b2, hm2_live⟩ :=
              hok _ _ _ hfull.subsumes (hpres _ _ _ hfull) l b1 hm1_live htouchF
            exact (hlive l (Or.inl (iff_of_true ⟨b1, hm1_live⟩ ⟨b2, hm2_live⟩))).mp ⟨bs, hbs_sim⟩
    · -- `h_var` lifts: same frame argument, without the value binding.
      intro t1 m1' x hbs_m2
      obtain ⟨m_sim, hbs_m1, hsub_sim, hlive⟩ := hbs_m2.simulate_down hsub hwf_e1
      refine ih_var hbs_m1 hsub_sim (fun _ _ _ h => h) ?_
        (Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes hbs_m1) hwf_e2)
          (match BigStep.wf_answer hbs_m1 hwf_e1 with
            | Exp.WfInHeap.wf_var hx => Subst.wf_openVar hx))
      intro t2 vc mc _ hbs_cont l bl hlk_l htouch
      by_cases hal : Trace.allocd t1 l
      · exact (hlive l (Or.inr hal)).mp ⟨bl, hlk_l⟩
      · rcases hm1 : m1.lookup l with _ | c
        · exact absurd (BigStep.live_appears_allocd hbs_m1 hm1 hlk_l) hal
        · obtain ⟨b1, hm1_live⟩ := Memory.mcell_lookup_down hbs_m1.subsumes hm1 hlk_l
          have htouchF : Trace.extTouches (t1 ++ t2) l :=
            Trace.extTouchesFrom_append_right hal (by simp) htouch
          have hfull := BigStep.bs_letin_var hbs_m1 hbs_cont
          obtain ⟨b2, hm2_live⟩ :=
            hok _ _ _ hfull.subsumes (hpres _ _ _ hfull) l b1 hm1_live htouchF
          exact (hlive l (Or.inl (iff_of_true ⟨b1, hm1_live⟩ ⟨b2, hm2_live⟩))).mp ⟨bl, hlk_l⟩
  | unpack _ h_ans h_val ih1 ih_val =>
    clear m1
    rename_i e1 e2 m1 _
    obtain ⟨hwf_e1, hwf_e2⟩ := Exp.wf_inv_unpack hwf
    have hok_e1 : ∀ t v m, m.subsumes m1 -> BigStep m1 e1 t v m ->
        Memory.SubsumeOk m1 t m2 := by
      intro t v m _ hbs1
      obtain ⟨hpk, hwf_v⟩ := h_ans _ _ _ hbs1
      cases hpk with
      | pack =>
        obtain ⟨t2, v2, mf, hbs2⟩ := (h_val hbs1).has_answer
        have hfull := BigStep.bs_unpack hbs1 hbs2
        exact (hok _ _ _ hfull.subsumes (hpres _ _ _ hfull)).mono_append
    refine Safe.unpack
      (ih1 (Q := fun t v m => BigStep m1 e1 t v m) hsub (fun _ _ _ h => h) hok_e1 hwf_e1)
      ?_ ?_
    · intro t1 v m1' hbs_m2
      obtain ⟨m_sim, hbs_m1, _, _⟩ := hbs_m2.simulate_down hsub hwf_e1
      exact ⟨(h_ans _ _ _ hbs_m1).1, BigStep.wf_answer hbs_m2 (Exp.wf_monotonic hsub hwf_e1)⟩
    · intro t1 m1' x cs hbs_m2
      obtain ⟨m_sim, hbs_m1, hsub_sim, hlive⟩ := hbs_m2.simulate_down hsub hwf_e1
      refine ih_val hbs_m1 hsub_sim (fun _ _ _ h => h) ?_
        (Exp.wf_subst (Exp.wf_monotonic (BigStep.subsumes hbs_m1) hwf_e2)
          (match BigStep.wf_answer hbs_m1 hwf_e1 with
            | Exp.WfInHeap.wf_pack hcs hx => Subst.wf_unpack hcs hx))
      intro t2 vc mc _ hbs_cont l bl hlk_l htouch
      by_cases hal : Trace.allocd t1 l
      · exact (hlive l (Or.inr hal)).mp ⟨bl, hlk_l⟩
      · rcases hm1 : m1.lookup l with _ | c
        · exact absurd (BigStep.live_appears_allocd hbs_m1 hm1 hlk_l) hal
        · obtain ⟨b1, hm1_live⟩ := Memory.mcell_lookup_down hbs_m1.subsumes hm1 hlk_l
          have htouchF : Trace.extTouches (t1 ++ t2) l :=
            Trace.extTouchesFrom_append_right hal (by simp) htouch
          have hfull := BigStep.bs_unpack hbs_m1 hbs_cont
          obtain ⟨b2, hm2_live⟩ :=
            hok _ _ _ hfull.subsumes (hpres _ _ _ hfull) l b1 hm1_live htouchF
          exact (hlive l (Or.inl (iff_of_true ⟨b1, hm1_live⟩ ⟨b2, hm2_live⟩))).mp ⟨bl, hlk_l⟩

/-- Memory-subsumption monotonicity of `Eval`.  `hok` carries the trace-footprint
  liveness: for every `Q`-result whose memory subsumes the source `m1`, the cells
  its trace touches that are live in `m1` remain live in `m2`. -/
theorem eval_monotonic {m1 m2 : Memory}
  (hpred : Q.is_monotonic)
  (_hbool : Q.is_bool_independent)
  (hsub : m2.subsumes m1)
  (hok : ∀ t v m, m.subsumes m1 -> Q t v m -> Memory.SubsumeOk m1 t m2)
  (hwf : Exp.WfInHeap e m1.heap)
  (heval : Eval m1 e Q) :
  Eval m2 e Q := by
  obtain ⟨hsafe1, hpres1⟩ := heval
  refine ⟨hsafe1.lift hsub hpres1 hok hwf, ?_⟩
  intro t v m2' hbs2
  obtain ⟨m1', hbs1, hsub', _⟩ := hbs2.simulate_down hsub hwf
  exact hpred (hbs1.wf_answer hwf) hsub' (hpres1 t v m1' hbs1)

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
  -- predicate is weakened along `himp` (each answer memory subsumes the start).
  obtain ⟨hsafe, hpres⟩ := heval
  refine ⟨hsafe, ?_⟩
  intro t v m' hbs
  exact himp m' hbs.subsumes t v (hpres t v m' hbs)

theorem eval_post_monotonic {Q1 Q2 : Tpost}
  (himp : Q1.entails Q2)
  (heval : Eval m e Q1) :
  Eval m e Q2 :=
  eval_post_monotonic_general (Tpost.entails_to_entails_after himp) heval

/- ============================================================================
   `Eval` INTRODUCTION COMBINATORS for `Eval := Safe ∧ preservation` (used by
   `Fundamental` as `apply Eval.eval_xxx`).  The `Safe` half uses the `Safe`
   constructors; the preservation half inverts the relational `BigStep`.
   ============================================================================ -/

/-- Lookup is a function, so two `val` lookups of the same location agree. -/
theorem Memory.lookup_val_eq {m : Memory} {x : Nat} {v1 v2 : HeapVal}
    (h1 : m.lookup x = some (.val v1)) (h2 : m.lookup x = some (.val v2)) : v1 = v2 :=
  Cell.val.inj (Option.some.inj (h1 ▸ h2))

/-- **A genuine step preserves liveness off its drop-footprint.**  Single-step analogue of
  `BigStep.frameLive`: every cell live before the step that the step does not externally drop is
  live after.  Only `step_drop` deallocates; the other leaves allocate/mutate/extend (preserving
  existing live cells), and the congruences recurse. -/
theorem Step.frameLive {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}}
    (hstep : Step t m1 e1 m2 e2) : Memory.FrameLive m1 t m2 := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ =>
    exact Memory.FrameLive.refl
  | step_write_true _ _ | step_write_false _ _ =>
    intro l b hlive _
    exact Memory.update_mcell_preserves_live _ ⟨b, hlive⟩
  | step_alloc _ hfr =>
    intro l b hlive _
    refine (Memory.extend_mcell_IsLive_ne ?_).mpr ⟨b, hlive⟩
    rintro rfl; exact absurd hlive (by simp [Memory.lookup, hfr])
  | step_drop _ =>
    intro l b hlive hnd
    refine (Memory.drop_mcell_IsLive_ne ?_).mpr ⟨b, hlive⟩
    rintro rfl; exact hnd (by simp [Trace.extDrops, Trace.extDropsFrom])
  | step_lift hv hwf hfr =>
    intro l b hlive _
    refine ⟨b, ?_⟩
    simp only [Memory.lookup, Memory.extend, Heap.extend] at hlive ⊢
    split
    · rename_i heq; rw [heq, hfr] at hlive; cases hlive
    · exact hlive
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ _ _ ih | step_par_right _ _ _ ih => exact ih

/-- `SeqStep` analogue of `Step.frameLive`: a sequential step preserves liveness off its
  drop-footprint.  Same proof — the memory transitions of `SeqStep` and `Step` coincide. -/
theorem SeqStep.frameLive {t : Trace} {m1 m2 : Memory} {e1 e2 : Exp {}}
    (hstep : SeqStep t m1 e1 m2 e2) : Memory.FrameLive m1 t m2 := by
  induction hstep with
  | step_apply _ | step_invoke _ _ | step_tapply _ | step_capply _ | step_unwrap _
  | step_cond_var_true _ | step_cond_var_false _ | step_read _ _
  | step_rename | step_unpack | step_par_join _ _ =>
    exact Memory.FrameLive.refl
  | step_write_true _ _ | step_write_false _ _ =>
    intro l b hlive _
    exact Memory.update_mcell_preserves_live _ ⟨b, hlive⟩
  | step_alloc _ hfr =>
    intro l b hlive _
    refine (Memory.extend_mcell_IsLive_ne ?_).mpr ⟨b, hlive⟩
    rintro rfl; exact absurd hlive (by simp [Memory.lookup, hfr])
  | step_drop _ =>
    intro l b hlive hnd
    refine (Memory.drop_mcell_IsLive_ne ?_).mpr ⟨b, hlive⟩
    rintro rfl; exact hnd (by simp [Trace.extDrops, Trace.extDropsFrom])
  | step_lift hv hwf hfr =>
    intro l b hlive _
    refine ⟨b, ?_⟩
    simp only [Memory.lookup, Memory.extend, Heap.extend] at hlive ⊢
    split
    · rename_i heq; rw [heq, hfr] at hlive; cases hlive
    · exact hlive
  | step_ctx_letin _ ih | step_ctx_unpack _ ih
  | step_par_left _ ih | step_par_right _ _ ih => exact ih

/-- **Branch-safety transports across a separated transition.**  If `e` is `Safe` at `ma` with its
  runs bounded by budget `B`, and `ma → ma'` keeps every live `B`-cell live (`hlive`), then `e` is
  `Safe` at `ma'`.  The frame condition `hlive` is supplied per-call from separation (the
  transition's footprint is disjoint from `B`) or compatibility (`is_compatible`).  Factors the
  `Safe.lift` boilerplate: a run's externally-touched cell is covered by `B`, hence in `B`. -/
theorem Safe.frame_lift {ma ma' : Memory} {e : Exp {}} {B : CapabilitySet}
    (hse : Safe ma e) (hsub : ma'.subsumes ma) (hwf : Exp.WfInHeap e ma.heap)
    (hbnd : ∀ {m' : Memory} {s : Trace} {v : Exp {}} {m''},
      m'.subsumes ma → Exp.WfInHeap e m'.heap → BigStep m' e s v m'' → TraceOk s B)
    (hlive : ∀ l b, (∃ mu, B.hasmem mu l) →
      ma.lookup l = some (.capability (.mcell b .live)) →
      ∃ b', ma'.lookup l = some (.capability (.mcell b' .live))) :
    Safe ma' e := by
  refine Safe.lift hse hsub (Q := fun s val m => BigStep ma e s val m)
    (fun _ _ _ h => h) ?_ hwf
  intro s v m _ hbs l b hl htouch
  have hnal : ¬ Trace.allocd s l := fun ha => by
    have := BigStep.alloc_fresh hbs ha; rw [hl] at this; cases this
  obtain ⟨cm, hext⟩ :=
    Trace.extTouchesMode_of_touched hnal (Trace.touched_of_extTouches htouch)
  obtain ⟨mu, hmem, _⟩ :=
    CapabilitySet.covers_imp_exists_hasmem
      ((hbnd (Memory.subsumes_refl _) hwf hbs).covers_of_extTouchesMode hext)
  exact hlive l b ⟨mu, hmem⟩ hl

/-- A `BigStep` from a simple value is the trivial no-op step. -/
theorem BigStep.simpleVal_eq {m : Memory} {v : Exp {}} {t v' m'}
    (hv : Exp.IsSimpleVal v) (hbs : BigStep m v t v' m') : t = [] ∧ v' = v ∧ m' = m := by
  cases hv <;> cases hbs <;> exact ⟨rfl, rfl, rfl⟩

theorem Eval.eval_pack {m : Memory} {cs : CaptureSet {}} {x : Var .var {}} {Q : Tpost}
    (hQ : Q [] (.pack cs x) m) : Eval m (.pack cs x) Q := by
  refine ⟨Safe.ans (Exp.IsAns.is_val Exp.IsVal.pack), ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_pack => exact hQ
  | bs_val hv => cases hv

theorem Eval.eval_var {m : Memory} {x : Var .var {}} {Q : Tpost}
    (hQ : Q [] (.var x) m) : Eval m (.var x) Q := by
  refine ⟨Safe.ans Exp.IsAns.is_var, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_var => exact hQ
  | bs_val hv => cases hv

theorem Eval.eval_val {m : Memory} {v : Exp {}} {Q : Tpost}
    (hv : Exp.IsSimpleVal v) (hQ : Q [] v m) : Eval m v Q := by
  refine ⟨Safe.ans (Exp.IsAns.is_val hv.to_IsVal), ?_⟩
  intro t v' m' hbs
  obtain ⟨rfl, rfl, rfl⟩ := BigStep.simpleVal_eq hv hbs
  exact hQ

theorem Eval.eval_read {m : Memory} {x : Nat} {y : Nat} {hv R} {b : Bool} {Q : Tpost}
    (hlkx : m.lookup x = some (.val ⟨.reader (.free y), hv, R⟩))
    (hlky : m.lookup y = some (.capability (.mcell b .live)))
    (hQ : ∀ b' : Bool, Q [.access .ro y] (if b' then .btrue else .bfalse) m) :
    Eval m (.read (.free x)) Q := by
  refine ⟨Safe.read hlkx hlky, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_read hlkx2 _ =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlkx hlkx2)
    simp only at heq
    cases heq
    exact hQ _
  | bs_val hv => cases hv

theorem Eval.eval_drop {m : Memory} {x : Nat} {b : Bool} {Q : Tpost}
    (hx : m.lookup x = some (.capability (.mcell b .live)))
    (hQ : Q [.dealloc x] .unit (m.drop_mcell x ⟨b, hx⟩)) :
    Eval m (.drop (.free x)) Q := by
  refine ⟨Safe.drop hx, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_drop hx2 => exact hQ
  | bs_val hv => cases hv

theorem Eval.eval_wrap {m : Memory} {cs : CaptureSet {}} {Ψ : ModalCtx {}} {e : Exp {}}
    {Q : Tpost} (hQ : Q [] (.boxed cs Ψ e) m) : Eval m (.boxed cs Ψ e) Q := by
  refine ⟨Safe.ans (Exp.IsAns.is_val Exp.IsVal.boxed), ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_wrap => exact hQ
  | bs_val _ => exact hQ

theorem Eval.eval_invoke {m : Memory} {x : Nat} {y : Nat} {hv R} {Q : Tpost}
    (hlkx : m.lookup x = some (.capability .basic))
    (hlky : m.lookup y = some (.val ⟨.unit, hv, R⟩))
    (hQ : Q [.access .epsilon x] .unit m) :
    Eval m (.app (.free x) (.free y)) Q := by
  refine ⟨Safe.invoke hlkx hlky, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_invoke hlkx2 hlky2 => exact hQ
  | bs_apply hlk2 _ => rw [hlkx] at hlk2; exact absurd hlk2 (by simp)
  | bs_val hv => cases hv

theorem Eval.eval_apply {m : Memory} {x : Nat} {y : Var .var {}} {cs T e hv R} {Q : Tpost}
    (hlk : m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩))
    (hrec : Eval m (e.subst (Subst.openVar y)) Q) :
    Eval m (.app (.free x) y) Q := by
  refine ⟨Safe.apply hlk hrec.1, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_apply hlk2 hbody =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
    simp only at heq; cases heq
    exact hrec.2 _ _ _ hbody
  | bs_invoke hlkx2 _ => rw [hlk] at hlkx2; exact absurd hlkx2 (by simp)
  | bs_val hv => cases hv

theorem Eval.eval_tapply {m : Memory} {x : Nat} {S} {cs T0 e hv R} {Q : Tpost}
    (hlk : m.lookup x = some (.val ⟨.tabs cs T0 e, hv, R⟩))
    (hrec : Eval m (e.subst (Subst.openTVar .top)) Q) :
    Eval m (.tapp (.free x) S) Q := by
  refine ⟨Safe.tapply hlk hrec.1, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_tapply hlk2 hbody =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
    simp only at heq; cases heq
    exact hrec.2 _ _ _ hbody
  | bs_val hv => cases hv

theorem Eval.eval_capply {m : Memory} {x : Nat} {CS} {cs B0 e hv R} {Q : Tpost}
    (hlk : m.lookup x = some (.val ⟨.cabs cs B0 e, hv, R⟩))
    (hrec : Eval m (e.subst (Subst.openCVar CS)) Q) :
    Eval m (.capp (.free x) CS) Q := by
  refine ⟨Safe.capply hlk hrec.1, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_capply hlk2 hbody =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
    simp only at heq; cases heq
    exact hrec.2 _ _ _ hbody
  | bs_val hv => cases hv

theorem Eval.eval_unwrap {m : Memory} {x : Nat} {cs Ψ e hv R} {Q : Tpost}
    (hlk : m.lookup x = some (.val ⟨.boxed cs Ψ e, hv, R⟩))
    (hrec : Eval m e Q) :
    Eval m (.unwrap (.free x)) Q := by
  refine ⟨Safe.unwrap hlk hrec.1, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_unwrap hlk2 hbody =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
    simp only at heq; cases heq
    exact hrec.2 _ _ _ hbody
  | bs_val hv => cases hv

theorem Eval.eval_write_true {m : Memory} {x y : Nat} {b0 : Bool} {hv R} {Q : Tpost}
    (hx : m.lookup x = some (.capability (.mcell b0 .live)))
    (hlky : m.lookup y = some (.val ⟨.btrue, hv, R⟩))
    (hQ : Q [.access .epsilon x] .unit (m.update_mcell x true .live ⟨b0, hx⟩)) :
    Eval m (.write (.free x) (.free y)) Q := by
  refine ⟨Safe.write_true hx hlky, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_write_true hx2 hlky2 => exact hQ
  | bs_write_false hx2 hlky2 =>
    exact absurd (congrArg HeapVal.unwrap (Memory.lookup_val_eq hlky hlky2)) (by simp)
  | bs_val hv => cases hv

theorem Eval.eval_write_false {m : Memory} {x y : Nat} {b0 : Bool} {hv R} {Q : Tpost}
    (hx : m.lookup x = some (.capability (.mcell b0 .live)))
    (hlky : m.lookup y = some (.val ⟨.bfalse, hv, R⟩))
    (hQ : Q [.access .epsilon x] .unit (m.update_mcell x false .live ⟨b0, hx⟩)) :
    Eval m (.write (.free x) (.free y)) Q := by
  refine ⟨Safe.write_false hx hlky, ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_write_false hx2 hlky2 => exact hQ
  | bs_write_true hx2 hlky2 =>
    exact absurd (congrArg HeapVal.unwrap (Memory.lookup_val_eq hlky hlky2)) (by simp)
  | bs_val hv => cases hv

theorem Eval.eval_alloc {m : Memory} {x : Nat} {b : Bool} {hv R} {Q : Tpost}
    (hlk : m.lookup x = some (.val ⟨if b then .btrue else .bfalse, hv, R⟩))
    (h_post : ∀ l (hfresh : m.heap l = none),
      Q [.alloc l] (.pack (.var (.M .epsilon) (.free l)) (.free l)) (m.extend_mcell l b hfresh)) :
    Eval m (.alloc (.free x)) Q := by
  refine ⟨Safe.alloc hlk, ?_⟩
  intro t v m' hbs
  cases hbs with
  | @bs_alloc _ _ b2 _ _ l2 hlk2 hfresh2 =>
    have heq := congrArg HeapVal.unwrap (Memory.lookup_val_eq hlk hlk2)
    simp only at heq
    have hbb : b = b2 := by cases b <;> cases b2 <;> simp_all
    subst hbb
    exact h_post l2 hfresh2
  | bs_val hv => cases hv

theorem Eval.eval_cond {m : Memory} {x : Var .var {}} {e2 e3 : Exp {}} {Q : Tpost}
    (hres : resolve m.heap (.var x) = some .btrue ∨ resolve m.heap (.var x) = some .bfalse)
    (h_true : resolve m.heap (.var x) = some .btrue → Eval m e2 Q)
    (h_false : resolve m.heap (.var x) = some .bfalse → Eval m e3 Q) :
    Eval m (.cond x e2 e3) Q := by
  refine ⟨Safe.cond hres (fun ht => (h_true ht).1) (fun hf => (h_false hf).1), ?_⟩
  intro t v m' hbs
  cases hbs with
  | bs_cond_true hres_t hbody => exact (h_true hres_t).2 _ _ _ hbody
  | bs_cond_false hres_f hbody => exact (h_false hres_f).2 _ _ _ hbody
  | bs_val hv => cases hv

/-- `par`: genuine interleaving.  The robust budget bounds (`hb1`/`hb2`), budget
  non-interference (`hni`), and robust right-branch safety (`hrs2`) are the
  separation content carried in `Safe.par`.  The trace postcondition runs on the
  sequential `bs_par` realization (`e1` to an answer, then `e2` from that
  answer-memory via `h2`); the result is always `.unit`. -/
theorem Eval.eval_par {m : Memory} {e1 e2 : Exp {}} {Q Q1 : Tpost}
    {Cs1 Cs2 : CaptureSet {}}
    (he1 : Eval m e1 Q1)
    (hse2 : Safe m e2)
    (hb1 : ∀ {m' : Memory} {t : Trace} {v : Exp {}} {m''},
      m'.subsumes m -> Exp.WfInHeap e1 m'.heap -> BigStep m' e1 t v m'' ->
      TraceOk t (Cs1.reachability m))
    (hb2 : ∀ {m' : Memory} {t : Trace} {v : Exp {}} {m''},
      m'.subsumes m -> Exp.WfInHeap e2 m'.heap -> BigStep m' e2 t v m'' ->
      TraceOk t (Cs2.reachability m))
    (hrs1 : ∀ {m' : Memory},
      m'.subsumes m -> m'.is_compatible (Cs1.reachability m) -> Safe m' e1)
    (hrs2 : ∀ {m' : Memory},
      m'.subsumes m -> m'.is_compatible (Cs2.reachability m) -> Safe m' e2)
    (hni : CapabilitySet.Noninterference (Cs1.reachability m) (Cs2.reachability m))
    (h2 : ∀ {t1 : Trace} {v1 : Exp {}} {m1 : Memory},
      m1.subsumes m -> Memory.FrameLive m t1 m1 -> Q1 t1 v1 m1 ->
      Eval m1 e2 (fun t2 _v2 m2 => Q (t1 ++ t2) .unit m2)) :
    Eval m (.par Cs1 Cs2 e1 e2) Q := by
  -- Instantiate the abstract carrier budget to the annotation's reachability; presence is
  -- exactly `reachability_dom`.
  refine ⟨Safe.par he1.1 hse2 ?_ hb1 hb2 hrs1 hrs2
    (fun _ _ h => CaptureSet.reachability_dom h)
    (fun _ _ h => CaptureSet.reachability_dom h)
    ⟨CapabilitySet.Subset.refl, CapabilitySet.Subset.refl⟩
    ⟨CapabilitySet.Subset.refl, CapabilitySet.Subset.refl⟩ hni, ?_⟩
  · intro t1 v1 m1 hrun
    exact (h2 hrun.subsumes hrun.frameLive (he1.2 t1 v1 m1 hrun)).1
  · intro t v m' hbs
    cases hbs with
    | bs_par hrun_e1 hrun_e2 =>
      exact (h2 hrun_e1.subsumes hrun_e1.frameLive (he1.2 _ _ _ hrun_e1)).2 _ _ _ hrun_e2
    | bs_val hv => cases hv

/-- `letin`: compose `e1`'s evaluation with the continuation.  Both halves run on
  the ACTUAL `e1`-answer (`he1.2`); `h_val`/`h_var` are handed the operational
  frame `FrameLive m t1 m1` (the `e1`-run keeps live cells alive unless its trace
  externally drops them). -/
theorem Eval.eval_letin {m : Memory} {e1 : Exp {}} {e2 : Exp ({},x)} {Q Q1 : Tpost}
    (_hpred : Q1.is_monotonic) (_hbool : Q1.is_bool_independent)
    (he1 : Eval m e1 Q1)
    (h_nonstuck : ∀ {t1 : Trace} {m1 : Memory} {v : Exp {}},
      Q1 t1 v m1 -> v.IsSimpleAns ∧ Exp.WfInHeap v m1.heap)
    (h_val : ∀ {t1 : Trace} {m1} {v : Exp {}}, m1.subsumes m -> Memory.FrameLive m t1 m1 ->
      (hv : Exp.IsSimpleVal v) -> (hwf_v : Exp.WfInHeap v m1.heap) -> Q1 t1 v m1 ->
      ∀ l' (hfresh : m1.lookup l' = none),
        Eval (m1.extend_val l' ⟨v, hv, compute_reachability m1.heap v hv⟩ hwf_v rfl hfresh)
          (e2.subst (Subst.openVar (.free l'))) (fun t2 => Q (t1 ++ t2)))
    (h_var : ∀ {t1 : Trace} {m1} {x : Var .var {}}, m1.subsumes m -> Memory.FrameLive m t1 m1 ->
      (hwf_x : x.WfInHeap m1.heap) -> Q1 t1 (.var x) m1 ->
      Eval m1 (e2.subst (Subst.openVar x)) (fun t2 => Q (t1 ++ t2))) :
    Eval m (.letin e1 e2) Q := by
  refine ⟨?_, ?_⟩
  · refine Safe.letin he1.1 (fun t1 v m1 hrun => h_nonstuck (he1.2 t1 v m1 hrun)) ?_ ?_
    · intro t1 m1 v hrun hv hwf_v l' hfresh
      exact (h_val (BigStep.subsumes hrun) (BigStep.frameLive hrun) hv hwf_v
        (he1.2 t1 v m1 hrun) l' hfresh).1
    · intro t1 m1 x hrun
      have hq1 := he1.2 t1 (.var x) m1 hrun
      have hwfx : x.WfInHeap m1.heap := by cases (h_nonstuck hq1).2 with | wf_var h => exact h
      exact (h_var (BigStep.subsumes hrun) (BigStep.frameLive hrun) hwfx hq1).1
  · intro t v m' hbs
    cases hbs with
    | bs_letin_val hrun_e1 hv hwf_v hfresh hrun_e2 =>
      exact (h_val (BigStep.subsumes hrun_e1) (BigStep.frameLive hrun_e1) hv hwf_v
        (he1.2 _ _ _ hrun_e1) _ hfresh).2 _ _ _ hrun_e2
    | bs_letin_var hrun_e1 hrun_e2 =>
      have hq1 := he1.2 _ _ _ hrun_e1
      cases (h_nonstuck hq1).2 with
      | wf_var hwfx =>
        exact (h_var (BigStep.subsumes hrun_e1) (BigStep.frameLive hrun_e1) hwfx hq1).2
          _ _ _ hrun_e2
    | bs_val hv => cases hv

/-- `unpack`: like `letin`, but the `e1`-answer is a `pack`. -/
theorem Eval.eval_unpack {m : Memory} {e1 : Exp {}} {e2 : Exp ({},C,x)} {Q Q1 : Tpost}
    (he1 : Eval m e1 Q1)
    (h_nonstuck : ∀ {t1 : Trace} {m1 : Memory} {v : Exp {}},
      Q1 t1 v m1 -> v.IsPack ∧ Exp.WfInHeap v m1.heap)
    (h_val : ∀ {t1 : Trace} {m1} {x : Var .var {}} {cs : CaptureSet {}}, m1.subsumes m ->
      Memory.FrameLive m t1 m1 ->
      (∀ {l c}, m.lookup l = none ->
        m1.lookup l = some (.capability c) -> Trace.allocd t1 l) ->
      (hwf_x : x.WfInHeap m1.heap) -> (hwf_cs : cs.WfInHeap m1.heap) -> Q1 t1 (.pack cs x) m1 ->
      Eval m1 (e2.subst (Subst.unpack cs x)) (fun t2 => Q (t1 ++ t2))) :
    Eval m (.unpack e1 e2) Q := by
  refine ⟨?_, ?_⟩
  · refine Safe.unpack he1.1 (fun t1 v m1 hrun => h_nonstuck (he1.2 t1 v m1 hrun)) ?_
    · intro t1 m1 x cs hrun
      have hq1 := he1.2 t1 (.pack cs x) m1 hrun
      cases (h_nonstuck hq1).2 with
      | wf_pack hcs hx =>
        exact (h_val (BigStep.subsumes hrun) (BigStep.frameLive hrun)
          (BigStep.appears_allocd_of_cap hrun) hx hcs hq1).1
  · intro t v m' hbs
    cases hbs with
    | bs_unpack hrun_e1 hrun_e2 =>
      have hq1 := he1.2 _ _ _ hrun_e1
      cases (h_nonstuck hq1).2 with
      | wf_pack hcs hx =>
        exact (h_val (BigStep.subsumes hrun_e1) (BigStep.frameLive hrun_e1)
          (BigStep.appears_allocd_of_cap hrun_e1) hx hcs hq1).2
          _ _ _ hrun_e2
    | bs_val hv => cases hv

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
