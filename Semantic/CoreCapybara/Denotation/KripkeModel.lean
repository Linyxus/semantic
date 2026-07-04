import Semantic.CoreCapybara.Semantics.Heap
import Semantic.CoreCapybara.Denotation.StepIndexedFlat

/-!
# Step-indexed Kripke worlds for a higher-order mutable store

## PROMOTED MODEL (Phase 1): see `Denotation/StepIndexedFlat.lean`

The `MonRel`/`StoreTyping`/`kdenot` construction below stores a *frozen* relation per cell
and exposes the cell agreement only as a one-way implication (`R → val Tc`).  That is enough
for `read`/`alloc` but NOT for `write`, which needs the backward direction — see the
`sem_typ_write` gap in `Fundamental.lean`.  Validating the keystone (Phase 1) revealed that
the dependent `World : Nat → Type` family with a content-fabricating `extend`
(`StepIndexedProto.lean`) cannot satisfy coherence at the index boundary.

The corrected, promoted store model is the **flat, truncation-based** one in
`Denotation/StepIndexedFlat.lean`: the cell agreement is a genuine biconditional below the
index (`∀ j < k, R j ↔ val_denot Tc j Ψ`), the keystone is **non-expansiveness**
(`val_denot_nonexpansive`: `val_denot T k` depends only on the world's `k`-approximation),
and BOTH `read_typed` (forward) and `write_reestablishes` (backward — the direction the
frozen model lacked) are proven, on the real `Ty`, for the `unit`/`cell`/**cell-of-arrow**
toy, `sorryAx`-free.  The frozen construction below is retained transitionally until Phase 2
ports `Denotation/Core.lean` onto the flat model.

## The problem

A generic cell `cell cs T` stores a heap *location* whose content must be a
`T`-value.  With a higher-order store, the predicate "`l`'s content is a `T`-value" is
not monotone under the naive future relation `Memory.subsumes` (a `write` changes the
content), and a faithful `read` (returning the content reference) cannot be replayed in
a subsuming memory.  This is the classical obstacle to a *monotone* logical relation
over an ML-style mutable store.

## Why a store typing alone is not enough (first-order vs. higher-order)

A **world** is a pair `(st, m)` with a *store typing* `st : Nat → Option (Ty .capt {})`
assigning a closed type to each mutable cell, and `MemTyped st m` ("every live cell's
content respects `st`").  The cell value relation records `st l = some T` (a *persistent*
fact) instead of pinning the content; this is what makes it monotone, and reading
recovers the content's type from `MemTyped`.

The earlier (first-order) version of this file made the value relation recurse
*structurally on the type* and claimed no step-indexing is needed.  That is sound only
for the reference fragment, because a **function** value's relation must quantify over
future worlds and require them well-typed (`MemTyped`) — and `MemTyped` calls the value
relation at *arbitrary* cell-content types (cells may store functions, cells-of-cells,
…).  So `val(arrow) → MemTyped → val(arbitrary content type)` has no well-founded
measure on the type: the classical higher-order-store obstruction.

## The retained frozen construction (`kdenot`, below)

`kdenot` adds a **step index** `k` ("well-typed for `k` more observation steps"): the
function case at index `k+1` quantifies over future worlds that are `MemTyped` at index `k`
and its body recurses at index `k`, so every recursive call decrements `k` (no recursion on
the *type* at the same index) and the definition is well-founded.  This breaks the
well-foundedness obstruction and supports `read`/`alloc`; it validates — on the real
`Ty`/`Memory` — monotonicity along `WorldLe` (free by transitivity for the function case),
downward closure in `k`, and that `read`/`alloc`/`write` read off / maintain the world's
well-typing, in place of the false syntactic `eval_monotonic`/`simulate_down`.

But its *cell* relation stores a frozen relation exposing only a one-way implication, so it
does NOT support `write` (see the top note); that is exactly why the promoted flat model
replaces it.  Capture-set coverage is omitted (orthogonal and already monotone).
-/

namespace CoreCapybara
namespace KripkeModel

/-- A **monotone** value relation: a memory-expression predicate stable under memory
growth (`subsumes`).  Every relation we ever store is a `val_denot` instance, hence
monotone (`val_denot_is_monotonic`); bundling the monotonicity proof with the relation
lets `MemTyped` be preserved under `subsumes` (`memTyped_subsumes`) and frees `alloc`/
`write` from an external `hmono` premise — without exposing the relation's origin. -/
def MonRel : Type := {R : Memory → Exp {} → Prop //
  ∀ m1 m2, m2.subsumes m1 → ∀ e, R m1 e → R m2 e}

/-- A **semantic** store typing assigns a *monotone* value relation (`MonRel`) to each
mutable cell location — substitution-stable, unlike a syntactic type.  The relation stored
at allocation is the world-instantiated content denotation. -/
abbrev StoreTyping := Nat → Option MonRel

/-- The typed future-world relation: the memory grows (`subsumes`) and the store typing
only grows (existing cells keep their assigned relation). -/
def WorldLe (st2 : StoreTyping) (m2 : Memory) (st1 : StoreTyping) (m1 : Memory) : Prop :=
  m2.subsumes m1 ∧ ∀ l R, st1 l = some R → st2 l = some R

theorem WorldLe.refl (st : StoreTyping) (m : Memory) : WorldLe st m st m :=
  ⟨Memory.subsumes_refl m, fun _ _ h => h⟩

theorem WorldLe.trans {st1 st2 st3 m1 m2 m3}
    (h12 : WorldLe st2 m2 st1 m1) (h23 : WorldLe st3 m3 st2 m2) : WorldLe st3 m3 st1 m1 :=
  ⟨Memory.subsumes_trans h23.1 h12.1, fun l T h => h23.2 l T (h12.2 l T h)⟩

/-- **The step-indexed value relation.**

Recursion is well-founded on the index `k`.  Base types and `cell`/`reader` consult only
the store typing `st` (never the content) — that is what keeps the cell relation
monotone — and do not recurse.  The `arrow` case quantifies over a *strictly smaller*
index `j < k` and over future worlds that are well-typed at `j` (the `MemTyped j` premise
inlined as the big `∀ l Tc n …`); its body recurses at `j`.  Every recursive call is at
`j < k`, so the definition is well-founded by recursion on `k`, and the `∀ j < k` shape
makes downward closure in the index free (`kdenot_down`).

NB (foundation stand-in): the real function *result* type `T2 : Ty .exi (∅,x)` is
existential and may mention the argument, so its denotation is `exi_exp_denot` of the
*opened* type — orthogonal machinery.  Here the codomain is modeled by the (closed)
domain type `T1` at a further future world, which is exactly the right shape to validate
the index-drop and the transitivity-based monotonicity; the integration into
`Denotation/Core.lean` substitutes the real `exi_exp_denot k` codomain. -/
def kdenot (k : Nat) (st : StoreTyping) (T : Ty .capt {}) (m : Memory) (e : Exp {}) : Prop :=
  match T with
  | .unit => resolve m.heap e = some .unit
  | .bool => resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse
  | .cell _ Tc =>
      ∃ l n ℓ R, e = .var (.free l) ∧
        m.lookup l = some (.capability (.mcell n ℓ)) ∧ st l = some R ∧
        (∀ m' e', R.1 m' e' → kdenot k st Tc m' e')
  | .reader _ Tc =>
      ∃ l n ℓ R, resolve m.heap e = some (.reader (.free l)) ∧
        m.lookup l = some (.capability (.mcell n ℓ)) ∧ st l = some R ∧
        (∀ m' e', R.1 m' e' → kdenot k st Tc m' e')
  | .arrow T1 _ _ =>
      ∃ cs0 T0 t0, resolve m.heap e = some (.abs cs0 T0 t0) ∧
        ∀ j, j < k → ∀ (st' : StoreTyping) (m' : Memory) (arg : Nat),
          WorldLe st' m' st m →
          (∀ l n R, st' l = some R →
            m'.lookup l = some (.capability (.mcell n .live)) →
            R.1 m' (.var (.free n))) →
          kdenot j st' T1 m' (.var (.free arg)) →
          ∀ (st'' : StoreTyping) (m'' : Memory),
            WorldLe st'' m'' st' m' → kdenot j st'' T1 m'' (.var (.free arg))
  | _ => True
termination_by (k, sizeOf T)
decreasing_by all_goals (simp_wf; try omega)

/-- A memory is **well-typed at index `k`** when every live mutable cell that `st` assigns
a relation `R` holds a value satisfying `R`.  The relation is applied directly — no
recursion through `kdenot` — which is what breaks the higher-order-store circularity. -/
def MemTyped (_k : Nat) (st : StoreTyping) (m : Memory) : Prop :=
  ∀ l n R, st l = some R → m.lookup l = some (.capability (.mcell n .live)) →
    R.1 m (.var (.free n))

/-- A mutable cell present in `m1` is present (as a mutable cell, of possibly decayed
liveness / changed content) in any subsuming `m2`.  This is why the existentially
quantified cell relation is monotone. -/
theorem mcell_up {m1 m2 : Memory} {l n ℓ} (hsub : m2.subsumes m1)
    (hl : m1.lookup l = some (.capability (.mcell n ℓ))) :
    ∃ n' ℓ', m2.lookup l = some (.capability (.mcell n' ℓ')) := by
  obtain ⟨c, hc, hsubc⟩ := hsub l _ hl
  cases c with
  | val => simp [Cell.subsumes] at hsubc
  | masked => simp [Cell.subsumes] at hsubc
  | capability info =>
    cases info with
    | basic => simp [Cell.subsumes] at hsubc
    | mcell n' ℓ' => exact ⟨n', ℓ', hc⟩

/-- **Monotonicity by construction.**  The value relation transports along the typed
future relation `WorldLe`, at every index.  `cell`/`reader` use `mcell_up` + store
growth; `arrow` is monotone *for free* by transitivity of `WorldLe` (the future-world
body at `(st1, m1)` already covers every world above `(st2, m2)`). -/
theorem kdenot_mono (T : Ty .capt {}) {k : Nat} {st1 st2 m1 m2} (hw : WorldLe st2 m2 st1 m1)
    (e : Exp {}) (ht : kdenot k st1 T m1 e) : kdenot k st2 T m2 e :=
  match T with
  | .cell cs Tc => by
      obtain ⟨hsub, hst⟩ := hw; unfold kdenot at ht ⊢
      obtain ⟨l, n, ℓ, R, he, hl, hstl, himpl⟩ := ht
      obtain ⟨n', ℓ', hl'⟩ := mcell_up hsub hl
      exact ⟨l, n', ℓ', R, he, hl', hst l R hstl,
        fun m' e' hR => kdenot_mono Tc ⟨Memory.subsumes_refl m', hst⟩ e' (himpl m' e' hR)⟩
  | .reader cs Tc => by
      obtain ⟨hsub, hst⟩ := hw; unfold kdenot at ht ⊢
      obtain ⟨l, n, ℓ, R, hres, hl, hstl, himpl⟩ := ht
      obtain ⟨n', ℓ', hl'⟩ := mcell_up hsub hl
      exact ⟨l, n', ℓ', R, resolve_monotonic hsub hres, hl', hst l R hstl,
        fun m' e' hR => kdenot_mono Tc ⟨Memory.subsumes_refl m', hst⟩ e' (himpl m' e' hR)⟩
  | .arrow T1 cs T2 => by
      obtain ⟨hsub, hst⟩ := hw; unfold kdenot at ht ⊢
      obtain ⟨cs0, T0, t0, hres, hbody⟩ := ht
      refine ⟨cs0, T0, t0, resolve_monotonic hsub hres, ?_⟩
      intro j hj st' m' arg hw' hmt harg st'' m'' hw''
      exact hbody j hj st' m' arg (WorldLe.trans ⟨hsub, hst⟩ hw') hmt harg st'' m'' hw''
  | .unit => by
      obtain ⟨hsub, _⟩ := hw; unfold kdenot at ht ⊢; exact resolve_monotonic hsub ht
  | .bool => by
      obtain ⟨hsub, _⟩ := hw; unfold kdenot at ht ⊢
      exact ht.imp (resolve_monotonic hsub) (resolve_monotonic hsub)
  | .top => by unfold kdenot at ht ⊢; exact ht
  | .tvar _ => by unfold kdenot at ht ⊢; exact ht
  | .cap _ => by unfold kdenot at ht ⊢; exact ht
  | .poly _ _ _ => by unfold kdenot at ht ⊢; exact ht
  | .cpoly _ _ _ => by unfold kdenot at ht ⊢; exact ht
  | .consumer _ _ _ => by unfold kdenot at ht ⊢; exact ht
  | .modal _ _ _ => by unfold kdenot at ht ⊢; exact ht
termination_by sizeOf T
decreasing_by all_goals (simp_wf; try omega)

/-- **Downward closure in the index.**  A `(k+1)`-step-typed value is `k`-step-typed:
the `arrow` case's `∀ j < k+1` body restricts to `∀ j < k`.  This is the standard
step-indexing monotonicity in the index. -/
theorem kdenot_down (st : StoreTyping) (T : Ty .capt {}) {k : Nat} (m : Memory)
    (e : Exp {}) (ht : kdenot (k + 1) st T m e) : kdenot k st T m e :=
  match T with
  | .cell cs Tc => by
      unfold kdenot at ht ⊢
      obtain ⟨l, n, ℓ, R, he, hl, hstl, himpl⟩ := ht
      exact ⟨l, n, ℓ, R, he, hl, hstl, fun m' e' hR => kdenot_down st Tc m' e' (himpl m' e' hR)⟩
  | .reader cs Tc => by
      unfold kdenot at ht ⊢
      obtain ⟨l, n, ℓ, R, hres, hl, hstl, himpl⟩ := ht
      exact ⟨l, n, ℓ, R, hres, hl, hstl, fun m' e' hR => kdenot_down st Tc m' e' (himpl m' e' hR)⟩
  | .arrow T1 cs T2 => by
      unfold kdenot at ht ⊢
      obtain ⟨cs0, T0, t0, hres, hbody⟩ := ht
      exact ⟨cs0, T0, t0, hres, fun j hj => hbody j (by omega)⟩
  | .top => by unfold kdenot at ht ⊢; exact ht
  | .tvar _ => by unfold kdenot at ht ⊢; exact ht
  | .cap _ => by unfold kdenot at ht ⊢; exact ht
  | .unit => by unfold kdenot at ht ⊢; exact ht
  | .bool => by unfold kdenot at ht ⊢; exact ht
  | .poly _ _ _ => by unfold kdenot at ht ⊢; exact ht
  | .cpoly _ _ _ => by unfold kdenot at ht ⊢; exact ht
  | .consumer _ _ _ => by unfold kdenot at ht ⊢; exact ht
  | .modal _ _ _ => by unfold kdenot at ht ⊢; exact ht
termination_by sizeOf T
decreasing_by all_goals (simp_wf; try omega)

/-- **Read soundness.**  At a well-typed world, dereferencing a live cell whose store
relation is `R` yields a value satisfying `R`.  Composed with the cell relation's
implication `R → kdenot … Tc`, this gives the faithful `read` its result type. -/
theorem read_typed {k st m l R n} (hwt : MemTyped k st m) (hst : st l = some R)
    (hl : m.lookup l = some (.capability (.mcell n .live))) :
    R.1 m (.var (.free n)) :=
  hwt l n R hst hl

/-- Extend a store typing with a fresh cell's relation. -/
def StoreTyping.set (st : StoreTyping) (l : Nat) (R : MonRel) : StoreTyping :=
  fun k => if k = l then some R else st k

/-- **Alloc steps up the world.**  Allocating a fresh cell `l` storing a location `c`
that already holds a `T`-value (at the current index), and typing `l` as `T`, yields a
world above the current one that is still well-typed at the same index. -/
theorem alloc_world {k : Nat} {st : StoreTyping} {m : Memory} {c : Nat}
    {R : MonRel} {l : Nat} (hfresh : m.heap l = none) (hstfresh : st l = none)
    (hcontent : m.heap c ≠ none)
    (hwt : MemTyped k st m)
    (hRext : R.1 (m.extend_mcell l c hfresh hcontent) (.var (.free c))) :
    WorldLe (st.set l R) (m.extend_mcell l c hfresh hcontent) st m ∧
      MemTyped k (st.set l R) (m.extend_mcell l c hfresh hcontent) := by
  have hsub : (m.extend_mcell l c hfresh hcontent).subsumes m :=
    Memory.extend_mcell_subsumes m l c hfresh hcontent
  have hwle : WorldLe (st.set l R) (m.extend_mcell l c hfresh hcontent) st m := by
    refine ⟨hsub, ?_⟩
    intro l' R' h
    unfold StoreTyping.set
    by_cases hl' : l' = l
    · subst hl'; rw [hstfresh] at h; cases h
    · rw [if_neg hl']; exact h
  refine ⟨hwle, ?_⟩
  intro l' n R' hst' hlk'
  unfold StoreTyping.set at hst'
  by_cases hl' : l' = l
  · rw [if_pos hl'] at hst'
    obtain rfl := Option.some.inj hst'
    rw [hl'] at hlk'
    have hlc := Memory.extend_mcell_lookup (m := m) (l := l) (n := c) hfresh hcontent
    have hcn : c = n :=
      (CapabilityInfo.mcell.inj (Cell.capability.inj (Option.some.inj (hlc.symm.trans hlk')))).1
    subst hcn
    exact hRext
  · rw [if_neg hl'] at hst'
    have hlk_old : m.lookup l' = some (.capability (.mcell n .live)) := by
      rw [← hlk']
      simp only [Memory.lookup, Memory.extend_mcell, Heap.extend_mcell, if_neg hl']
    -- existing cell `l'` is unchanged by the extension; its bundled monotonicity transports
    exact R'.2 m _ hsub _ (hwt l' n R' hst' hlk_old)

/-- **Write steps up the world (type-preservingly).**  Writing a value `y` satisfying the
cell's store relation `R` keeps the store typing fixed, yields a subsuming memory, and
preserves well-typing — the type-preserving update a naive `subsumes` cannot track. -/
theorem write_world {k : Nat} {st : StoreTyping} {m : Memory} {l : Nat}
    {R : MonRel} {y n0 : Nat}
    (hexists : m.lookup l = some (.capability (.mcell n0 .live)))
    (hcontent : Liveness.live = .live → m.heap y ≠ none)
    (hst : st l = some R) (hwt : MemTyped k st m)
    (hyR : R.1 (m.update_mcell l y .live ⟨n0, hexists⟩ hcontent) (.var (.free y))) :
    WorldLe st (m.update_mcell l y .live ⟨n0, hexists⟩ hcontent) st m ∧
      MemTyped k st (m.update_mcell l y .live ⟨n0, hexists⟩ hcontent) := by
  have hsub : (m.update_mcell l y .live ⟨n0, hexists⟩ hcontent).subsumes m :=
    Memory.update_mcell_subsumes m l y .live ⟨n0, hexists⟩ hcontent
  have hwle : WorldLe st (m.update_mcell l y .live ⟨n0, hexists⟩ hcontent) st m :=
    ⟨hsub, fun _ _ h => h⟩
  refine ⟨hwle, ?_⟩
  intro l' n R' hst' hlk'
  by_cases hl' : l' = l
  · rw [hl'] at hst' hlk'
    rw [hst] at hst'
    obtain rfl := Option.some.inj hst'
    have hlu : (m.update_mcell l y .live ⟨n0, hexists⟩ hcontent).lookup l
        = some (.capability (.mcell y .live)) := by
      simp [Memory.lookup, Memory.update_mcell, Heap.update_cell]
    have hyn : y = n :=
      (CapabilityInfo.mcell.inj (Cell.capability.inj (Option.some.inj (hlu.symm.trans hlk')))).1
    subst hyn
    exact hyR
  · have hlk_old : m.lookup l' = some (.capability (.mcell n .live)) := by
      rw [← hlk']
      simp only [Memory.lookup, Memory.update_mcell, Heap.update_cell, if_neg hl']
    -- the written cell is `l ≠ l'`, so `l'`'s content is unchanged; transport via `R'.2`
    exact R'.2 m _ hsub _ (hwt l' n R' hst' hlk_old)

/-! ## The payoff: monotonicity becomes structural

The expression relation the Fundamental theorem needs is the **future-quantified** form
below: an expression is good if, at every accessible future world that is well-typed (at
the appropriate index), it behaves well.  Its monotonicity is *free* — pure transitivity
of `WorldLe` — with no operational replay (`simulate_down`) at all. -/

/-- A future-quantified, step-indexed predicate (schematic stand-in for the expression
denotation): `P k st m e` is whatever the Fundamental theorem asserts about evaluating
`e` at the `k`-well-typed world `(st, m)`. -/
def Robust (P : Nat → StoreTyping → Memory → Exp {} → Prop)
    (k : Nat) (st : StoreTyping) (m : Memory) (e : Exp {}) : Prop :=
  ∀ st' m', WorldLe st' m' st m → MemTyped k st' m' → P k st' m' e

/-- **Monotonicity, for free.**  Any future-quantified expression property is monotone
along `WorldLe` by transitivity alone — the structural replacement for `eval_monotonic`/
`simulate_down`, valid at every index. -/
theorem Robust.mono {P k} {st1 st2 m1 m2} (hw : WorldLe st2 m2 st1 m1) {e} :
    Robust P k st1 m1 e → Robust P k st2 m2 e :=
  fun h st' m' hw' hwt => h st' m' (WorldLe.trans hw hw') hwt

/-- The future-quantified form refines the present: instantiate at the current world. -/
theorem Robust.here {P k st m e} (hwt : MemTyped k st m) (h : Robust P k st m e) :
    P k st m e :=
  h st m (WorldLe.refl st m) hwt

/-! ## Integration plan (how this slots into the real development)

The validated pieces above are the *whole* step-indexed model for higher-order-store
soundness.  To close `sem_typ_read`/`sem_typ_alloc`/`sem_typ_write` and delete the false
`eval_monotonic`/`simulate_down`/`Safe.lift`/`Safe.frame_lift`:

1. **Thread `(k, st)`.**  Give `Denot` an index and a store typing
   (`Denot := Nat → StoreTyping → Memory → Exp → Prop`).  `Memory`/`Heap`/`BigStep`/
   `SmallStep` are untouched (only the *Denotation* layer changes — `Eval` is generic
   over its postcondition).

2. **Rewrite `val_denot` cells/readers/arrows** along `kdenot` here: cells/readers record
   `st l = some T` (persistent); the `arrow`/`poly`/`cpoly`/`modal` future-world
   quantifiers carry `MemTyped k` and drop to index `k`.

3. **Replace `is_monotonic` (over `subsumes`) with monotonicity over `WorldLe`**: the
   reference cases become `kdenot_mono`, the function cases are the existing proofs plus
   a `WorldLe.trans` step; downward closure in `k` is `kdenot_down`.

4. **Carry `MemTyped` as the world's well-typedness** in `Eval`/`exp_denot`.  `read`'s
   soundness in the Fundamental theorem is `read_typed`; `alloc`/`write` maintain the
   world by `alloc_world`/`write_world` (note both take the content-presence witness the
   generic `extend_mcell`/`update_mcell` require, matching `Memory.mcell_wf`).

5. **Define `exp_denot` future-quantified** (`Robust` shape).  `exp_denot_is_monotonic`
   collapses to `Robust.mono`; the operational monotonicity lemmas in `BigStep.lean` are
   then unused and deleted.

The step index makes the construction sound for the *full* higher-order store; recursion
is structural on `k`, so the relation stays a plain well-founded Lean definition — as
this file proves end to end. -/

end KripkeModel
end CoreCapybara
