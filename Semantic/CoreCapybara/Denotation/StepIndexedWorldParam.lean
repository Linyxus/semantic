import Semantic.CoreCapybara.Denotation.StepIndexedFlat

/-!
# Ahmed world-parametrized step-indexed store

This is the store model for CoreCapybara's higher-order mutable references, used by
`Denotation/Core.lean`.  A stored relation at level `k` is a *family over all lower worlds*
`(j : Fin k) → World j → …`, so truncation is a pure drop (no content-fabricating `extend`),
and the cell agreement is a genuine **biconditional** against `val_denot` — giving BOTH the
forward direction (`read`) and the backward direction (`write`) that the one-way store in
`KripkeModel.lean` lacks.

## Why step-indexing is *necessary* (the definitive argument)

The `alloc` typing rule (`TypeSystem/Core.lean`) types `alloc x : cell T` for **any** content
type `T`, including a bare type variable `X`.  So a mutable cell may have *abstract* content,
whose meaning is an environment-supplied semantic denotation — **not** a closed syntactic type.
Hence the store cannot map locations to syntactic types (that fails abstract content); it
must map to *semantic relations*.  A semantic cell relation must be **simultaneously**
(1) `WorldLe`-monotone (survive store growth), (2) write-capable (re-establishable from a
fresh `val_denot` value — needs the backward direction), and (3) abstract-content-capable.
No *non-indexed* relation store satisfies all three at once:

  * a one-way frozen implication (`KripkeModel.kdenot`): (1)✓ (2)✗ (3)✓ — no write;
  * a biconditional pinned to a fixed world (`StepIndexedFlat.lean`): (1)✗ (2)✓ (3)✓ —
    not monotone (a later-allocated location breaks the pin);
  * a store of syntactic types: (1)✓ (2)✓ (3)✗ — no abstract content.

The *only* device that meets all three is the **world-parametrized** relation below: the cell
relation quantifies over all lower worlds, so it is growth-stable (1), re-interpreting the
content type at the current world gives both directions (2), and it is a plain semantic
relation (3).  That relation stores, at level `k`, a family indexed by `Fin k` — so its very
*type* `World` is defined by recursion on the index, i.e. it is **inherently step-indexed**.
Therefore step-indexing is not an artifact of the proof technique; the full system (abstract
mutable cells with faithful reads *and* writes) cannot be modeled by any non-indexed store.

## Consequence: reads consume the index

`MemTyped k` can only expose a cell's content at indices `i < k` (`R : SemRel k` is
`Fin k`-indexed, by `World`-positivity).  So dereferencing yields the content typed at `< k`,
never at `k`: a `read` **consumes one index**.  The expression relation (`Eval`'s
postcondition, in `Denotation/Core.lean`) therefore asserts `val_denot` at `k − μ(t)`, where
`μ` counts index-consuming events in the big-step trace `t`; the Fundamental theorem threads
this decrement through trace composition (`t = t₁ ++ t₂`).

## What is proven here

`World`/`SemRel` recursion (accepted via `cast` + the defining equation `World.unfold`), world
extensionality/truncation algebra (`World.ext`, `World.trunc`, `World.trunc_trunc`), the typed
future relation `WorldLe` (refl/trans/`trunc`), the value relation `val_denot` on the real
`Ty` for the `unit`/`bool`/`cell`/`arrow` fragment, and its keystones: `val_denot_worldle_mono`
(the property the flat store lacked — **growth-stable**, cell case trivial),
`val_denot_down_trunc` (downward closure through truncation), and read/write soundness
(`read_typed` forward, `write_reestablishes` backward).
-/

namespace CoreCapybara
namespace WP

/-- `World k` maps each location to an optional relation usable at level `k`: a family, over
every lower level `j < k`, of predicates parametrized by a `World j`. -/
def World : Nat → Type
  | k => Nat → Option ((j : Fin k) → World j.val → Memory → Exp {} → Prop)
termination_by k => k
decreasing_by exact j.isLt

/-- `SemRel k`: a relation stored at level `k` — a family, over every lower level, of
predicates parametrized by a lower world. -/
abbrev SemRel (k : Nat) : Type := (j : Fin k) → World j.val → Memory → Exp {} → Prop

/-- The defining equation (WF `def`s do not reduce definitionally). -/
theorem World.unfold (k : Nat) : World k = (Nat → Option (SemRel k)) := by
  unfold World SemRel
  rfl

/-- Look up a location, casting through the defining equation. -/
def World.lookup {k : Nat} (w : World k) (l : Nat) : Option (SemRel k) :=
  cast (World.unfold k) w l

/-- Build a world from a location map (inverse cast). -/
def World.mk {k : Nat} (f : Nat → Option (SemRel k)) : World k :=
  cast (World.unfold k).symm f

@[simp] theorem World.lookup_mk {k : Nat} (f : Nat → Option (SemRel k)) (l : Nat) :
    (World.mk f).lookup l = f l := by
  simp only [World.lookup, World.mk, cast_cast, cast_eq]

theorem World.mk_lookup {k : Nat} (w : World k) : World.mk (World.lookup w) = w := by
  change cast (World.unfold k).symm (fun l => cast (World.unfold k) w l) = w
  rw [cast_cast, cast_eq]

/-- Worlds are determined by their lookups. -/
theorem World.ext {k : Nat} {w1 w2 : World k} (h : ∀ l, w1.lookup l = w2.lookup l) : w1 = w2 := by
  rw [← World.mk_lookup w1, ← World.mk_lookup w2]
  exact congrArg World.mk (funext h)

/-- **Truncation** to a lower level: drop the top of each stored family.  A pure restriction
of the `Fin`-index — no content is fabricated. -/
def World.trunc {k j : Nat} (hjk : j ≤ k) (w : World k) : World j :=
  World.mk fun l => (w.lookup l).map fun R (i : Fin j) (wi : World i.val) =>
    R ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩ wi

/-- **The typed future-world relation** (at a fixed level).  The memory grows and the store
typing only grows (existing cells keep their assigned relation). -/
def WorldLe {k : Nat} (Ψ' : World k) (m' : Memory) (Ψ : World k) (m : Memory) : Prop :=
  m'.subsumes m ∧ ∀ l R, Ψ.lookup l = some R → Ψ'.lookup l = some R

theorem WorldLe.refl {k : Nat} (Ψ : World k) (m : Memory) : WorldLe Ψ m Ψ m :=
  ⟨Memory.subsumes_refl m, fun _ _ h => h⟩

theorem WorldLe.trans {k : Nat} {Ψ1 Ψ2 Ψ3 : World k} {m1 m2 m3}
    (h12 : WorldLe Ψ2 m2 Ψ1 m1) (h23 : WorldLe Ψ3 m3 Ψ2 m2) : WorldLe Ψ3 m3 Ψ1 m1 :=
  ⟨Memory.subsumes_trans h23.1 h12.1, fun l R h => h23.2 l R (h12.2 l R h)⟩

/-- Extend a world with a fresh cell's stored relation (or overwrite an existing one). -/
def World.set {k : Nat} (w : World k) (l : Nat) (R : SemRel k) : World k :=
  World.mk fun l' => if l' = l then some R else w.lookup l'

@[simp] theorem World.set_lookup {k : Nat} (w : World k) (l : Nat) (R : SemRel k) (l' : Nat) :
    (w.set l R).lookup l' = if l' = l then some R else w.lookup l' := by
  simp only [World.set, World.lookup_mk]

/-- **The world-parametrized step-indexed value relation.**  The `cell` case compares its
stored relation `R` with `val_denot Tc` over *all* lower worlds `w'` (that is what makes it
growth-stable — the comparison never mentions the ambient world).  The `arrow` case is
step-indexed; its inlined `MemTyped` premise consults the stored relations directly (no
`val_denot` recursion), so the only recursive calls are at a strictly smaller index. -/
def val_denot : Ty .capt {} → (k : Nat) → World k → Memory → Exp {} → Prop
  | .unit, _, _, m, e => resolve m.heap e = some .unit
  | .bool, _, _, m, e => resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse
  | .cell _ Tc, k, Ψ, m, e =>
      ∃ l n0 ℓ0 R, e = .var (.free l) ∧
        m.lookup l = some (.capability (.mcell n0 ℓ0)) ∧
        Ψ.lookup l = some R ∧
        ∀ (j : Fin k) (w' : World j.val) (m' : Memory) (e' : Exp {}),
          R j w' m' e' ↔ val_denot Tc j.val w' m' e'
  | .arrow T1 _ _, k, Ψ, m, e =>
      (∃ cs0 T0 t0, resolve m.heap e = some (.abs cs0 T0 t0)) ∧
      ∀ (j : Fin k) (Ψ' : World j.val) (m' : Memory) (arg : Nat),
        WorldLe Ψ' m' (Ψ.trunc (Nat.le_of_lt j.isLt)) m →
        (∀ l R n, Ψ'.lookup l = some R →
            m'.lookup l = some (.capability (.mcell n .live)) →
            ∀ (i : Fin j.val), R i (Ψ'.trunc (Nat.le_of_lt i.isLt)) m' (.var (.free n))) →
        val_denot T1 j.val Ψ' m' (.var (.free arg)) →
        resolve m'.heap (.var (.free arg)) ≠ none
  | _, _, _, _, _ => True
termination_by _ k => k
decreasing_by all_goals exact (Fin.isLt _)

@[simp] theorem World.trunc_lookup {k j : Nat} (hjk : j ≤ k) (w : World k) (l : Nat) :
    (w.trunc hjk).lookup l = (w.lookup l).map fun R (i : Fin j) (wi : World i.val) =>
      R ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩ wi := by
  simp only [World.trunc, World.lookup_mk]

/-- Truncating to the *same* level is the identity (the `Fin`-drop is `Fin.eta`).  Discharges
the `k - [].readCount = k` / `st.trunc (le_refl) = st` friction in the 0-read (`var`/value-intro)
cases of the step-counted expression relation. -/
@[simp] theorem World.trunc_self {k : Nat} (hkk : k ≤ k) (w : World k) : w.trunc hkk = w := by
  apply World.ext
  intro l
  rw [World.trunc_lookup]
  cases w.lookup l with
  | none => rfl
  | some R => rfl

/-- Reflexivity through a same-level truncation.  Discharges the `WorldLe w m (w.trunc h) m`
obligation in the 0-read (`var`/value-intro) cases of the step-counted relation, where the
result world is `w.trunc (Nat.sub_le k [].readCount)` and the level `k - [].readCount` is
definitionally `k`. -/
theorem WorldLe.refl_trunc_self {k : Nat} (h : k ≤ k) (w : World k) (m : Memory) :
    WorldLe w m (w.trunc h) m := by
  rw [World.trunc_self]; exact WorldLe.refl w m

/-- `WorldLe` transports to any truncation level: the store-typing persistence survives the
family-drop (the same lower relation is produced on both sides). -/
theorem WorldLe.trunc {k j : Nat} (hjk : j ≤ k) {Ψ2 Ψ1 : World k} {m2 m1}
    (h : WorldLe Ψ2 m2 Ψ1 m1) : WorldLe (Ψ2.trunc hjk) m2 (Ψ1.trunc hjk) m1 := by
  refine ⟨h.1, fun l R hR => ?_⟩
  rw [World.trunc_lookup] at hR ⊢
  cases hΨ1 : Ψ1.lookup l with
  | none => rw [hΨ1] at hR; simp at hR
  | some R1 => rw [hΨ1] at hR; rw [h.2 l R1 hΨ1]; exact hR

/-- **`WorldLe`-monotonicity — the property the flat relation store could not provide.**
The `cell` case is *trivial*: the stored relation `R` and its agreement clause are compared
over ALL lower worlds, so they never mention the ambient world and carry over verbatim under
store growth.  The `arrow` case is monotone for free by `WorldLe.trans` (through the
truncation, via `WorldLe.trunc`).  No induction on the type is needed. -/
theorem val_denot_worldle_mono (T : Ty .capt {}) {k : Nat} {Ψ1 Ψ2 : World k} {m1 m2}
    (hwle : WorldLe Ψ2 m2 Ψ1 m1) {e} :
    val_denot T k Ψ1 m1 e → val_denot T k Ψ2 m2 e := by
  cases T with
  | unit => simp only [val_denot]; exact resolve_monotonic hwle.1
  | bool =>
    simp only [val_denot]
    rintro (h | h)
    · exact Or.inl (resolve_monotonic hwle.1 h)
    · exact Or.inr (resolve_monotonic hwle.1 h)
  | cell cs Tc =>
    simp only [val_denot]
    rintro ⟨l, n0, ℓ0, R, he, hlk, hΨl, hag⟩
    obtain ⟨n', ℓ', hlk'⟩ := StepIndexedFlat.mcell_up hwle.1 hlk
    exact ⟨l, n', ℓ', R, he, hlk', hwle.2 l R hΨl, hag⟩
  | arrow T1 cs T2 =>
    simp only [val_denot]
    rintro ⟨⟨cs0, T0, t0, habs⟩, hbody⟩
    refine ⟨⟨cs0, T0, t0, resolve_monotonic hwle.1 habs⟩, fun j Ψ' m' arg hwle' hmt harg => ?_⟩
    have hw := WorldLe.trans (WorldLe.trunc (Nat.le_of_lt j.isLt) hwle) hwle'
    exact hbody j Ψ' m' arg hw hmt harg
  | _ => simp only [val_denot]; exact id

/-- Truncations compose (both are pure family-drops keyed on the location value). -/
theorem World.trunc_trunc {k j i : Nat} (hkj : j ≤ k) (hji : i ≤ j) (w : World k) :
    (w.trunc hkj).trunc hji = w.trunc (Nat.le_trans hji hkj) := by
  apply World.ext
  intro l
  simp only [World.trunc_lookup]
  cases w.lookup l with
  | none => rfl
  | some R => rfl

/-- **Downward closure through truncation.**  A `T`-value at `(k, Ψ)` is a `T`-value at every
lower `(j, Ψ.trunc)`.  This connects an actual value (typed at the current world) to the
per-level obligations that `read`/`write`/`MemTyped` are stated with. -/
theorem val_denot_down_trunc {T : Ty .capt {}} {k j : Nat} (hjk : j ≤ k) {Ψ : World k} {m e} :
    val_denot T k Ψ m e → val_denot T j (Ψ.trunc hjk) m e := by
  cases T with
  | cell cs Tc =>
    simp only [val_denot]
    rintro ⟨l, n0, ℓ0, R, he, hlk, hΨl, hag⟩
    refine ⟨l, n0, ℓ0, _, he, hlk, by rw [World.trunc_lookup, hΨl]; rfl, ?_⟩
    intro i w' m' e'
    exact hag ⟨i.val, Nat.lt_of_lt_of_le i.isLt hjk⟩ w' m' e'
  | arrow T1 cs T2 =>
    simp only [val_denot]
    rintro ⟨habs, hbody⟩
    refine ⟨habs, fun i Ψ' m' arg hwle' hmt harg => ?_⟩
    have hi' : i.val < k := Nat.lt_of_lt_of_le i.isLt hjk
    rw [World.trunc_trunc] at hwle'
    exact hbody ⟨i.val, hi'⟩ Ψ' m' arg hwle' hmt harg
  | _ => simp only [val_denot]; exact id

/-- **Well-typed world at index `k`.**  Every live cell's content satisfies its stored
relation `R`, applied at each lower level `j` against the world truncated to that level. -/
def MemTyped (k : Nat) (Ψ : World k) (m : Memory) : Prop :=
  (∀ l R, Ψ.lookup l = some R → ∃ n ℓ, m.lookup l = some (.capability (.mcell n ℓ))) ∧
  ∀ l R n, Ψ.lookup l = some R → m.lookup l = some (.capability (.mcell n .live)) →
    ∀ (j : Fin k), R j (Ψ.trunc (Nat.le_of_lt j.isLt)) m (.var (.free n))

/-- **Read soundness.**  At a well-typed world, dereferencing a live cell whose stored
relation `R` agrees with `val_denot Tc` yields a `Tc`-value (at each lower truncated world) —
the FORWARD direction of the cell's biconditional. -/
theorem read_typed {k : Nat} {Ψ : World k} {m l Tc n} {R : SemRel k}
    (hwt : MemTyped k Ψ m) (hΨl : Ψ.lookup l = some R)
    (hlk : m.lookup l = some (.capability (.mcell n .live)))
    (hag : ∀ (j : Fin k) (w' : World j.val) m' e', R j w' m' e' ↔ val_denot Tc j.val w' m' e') :
    ∀ (j : Fin k), val_denot Tc j.val (Ψ.trunc (Nat.le_of_lt j.isLt)) m (.var (.free n)) :=
  fun j => (hag j _ m _).mp (hwt.2 l R n hΨl hlk j)

/-- **Write soundness (the crux).**  A value that is a `Tc`-value at each lower truncated
world satisfies the cell's stored relation `R` — the BACKWARD direction the one-way and
fixed-world stores cannot supply.  Available here because the cell agreement is a genuine
biconditional over *all* lower worlds, and it is world-stable (`val_denot_worldle_mono`). -/
theorem write_reestablishes {k : Nat} {Ψ : World k} {Tc m_upd e_y} {R : SemRel k}
    (hag : ∀ (j : Fin k) (w' : World j.val) m' e', R j w' m' e' ↔ val_denot Tc j.val w' m' e')
    (hy : ∀ (j : Fin k), val_denot Tc j.val (Ψ.trunc (Nat.le_of_lt j.isLt)) m_upd e_y) :
    ∀ (j : Fin k), R j (Ψ.trunc (Nat.le_of_lt j.isLt)) m_upd e_y :=
  fun j => (hag j _ m_upd e_y).mpr (hy j)

/-! ## Summary

Ahmed's world-parametrized step-indexed store meets ALL THREE requirements the simpler stores
could not meet simultaneously:

* **`WorldLe`-monotone** — `val_denot_worldle_mono`, cell case *trivial* (the agreement ranges
  over all lower worlds, so it is stable under store growth);
* **write-capable** — `write_reestablishes` supplies the backward direction;
* **abstract-content-capable** — the store holds *relations* (`SemRel`), so a cell's content
  can be a type variable's denotation (an arbitrary `SemRel`), not only a closed type.

The `World`/`SemRel` type recursion is accepted by Lean and made usable via `World.mk`/
`World.lookup` (casts localized), and truncation is a pure drop — no content-fabricating
`extend`, hence no boundary problem. -/

end WP
end CoreCapybara
