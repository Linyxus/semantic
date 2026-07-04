import Semantic.CoreCapybara.Denotation.StepIndexedFlat

/-!
# Step-indexed **syntactic-type** store world (sandbox / design validation)

Phase-2 attempt surfaced a genuine gap in the flat *relation* store (`StepIndexedFlat.lean`):
its cell relation is a biconditional `R j ↔ val_denot Tc j Ψ` pinned to a *fixed* world `Ψ`,
so it is **not monotone under store growth** (`WorldLe`).  Concretely, a cell value can be
written/held whose content references a location allocated *later*; the frozen relation `R`
cannot see that location, so `R j ↔ val_denot Tc j Ψ'` fails at the grown world `Ψ'`.  The
current `Core.lean` avoids this only by storing a *one-way* implication (monotone, but no
`write`).  Neither a one-way nor a frozen-biconditional *relation* is both monotone and
write-capable — see `Core.val_denot_worldle_mono` (cell case uses only the forward direction).

## The fix: store **types**, not relations (Ahmed *syntactic* step-indexed LR)

Map each location to the (closed, syntactic) content **type**, and re-interpret it with
`val_denot` at whatever world is current.  A syntactic type is trivially stable under store
growth, and re-interpreting at the current world gives BOTH directions (read and write) for
free.  The higher-order-store circularity (`val_denot(arrow) → MemTyped → val_denot(any Tc)`)
is broken by the **step index**: the well-typedness premise `MemTyped j` in the function case
consults `val_denot` only at `i < j`, so every recursive call is at a strictly smaller index.

This sandbox validates the property the flat store lacked — **`WorldLe`-monotonicity of the
cell** — plus read and write, on the `unit`/`cell`/`arrow` toy.
-/

namespace CoreCapybara
namespace StepIndexedTypeStore

open StepIndexedFlat (mcell_up)

/-- A **syntactic-type store typing**: each location maps to its closed content type. -/
abbrev TWorld : Type := Nat → Option (Ty .capt {})

/-- Typed future world: memory grows and the store typing only grows (fixed types). -/
def WorldLe (Ψ' : TWorld) (m' : Memory) (Ψ : TWorld) (m : Memory) : Prop :=
  m'.subsumes m ∧ ∀ l Tc, Ψ l = some Tc → Ψ' l = some Tc

theorem WorldLe.refl (Ψ : TWorld) (m : Memory) : WorldLe Ψ m Ψ m :=
  ⟨Memory.subsumes_refl m, fun _ _ h => h⟩

theorem WorldLe.trans {Ψ1 Ψ2 Ψ3 m1 m2 m3} (h12 : WorldLe Ψ2 m2 Ψ1 m1)
    (h23 : WorldLe Ψ3 m3 Ψ2 m2) : WorldLe Ψ3 m3 Ψ1 m1 :=
  ⟨Memory.subsumes_trans h23.1 h12.1, fun l Tc h => h23.2 l Tc (h12.2 l Tc h)⟩

/-- **The step-indexed value relation over a type store.**  The `cell` case is index-agnostic
and stores only the fact "`l`'s content type is `Tc`" — trivially stable under `WorldLe`.  The
`arrow` case is genuinely step-indexed: it quantifies over `j < k`, future worlds, and worlds
well-typed at `j` (the inlined `MemTyped`, which consults `val_denot` only at `i < j`).  Every
recursive call is at a strictly smaller index, so recursion is well-founded on `k`. -/
def val_denot : Ty .capt {} → Nat → TWorld → Memory → Exp {} → Prop
  | .unit, _, _, m, e => resolve m.heap e = some .unit
  | .bool, _, _, m, e => resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse
  | .cell _ Tc, _, Ψ, m, e =>
      ∃ l n0 ℓ0, e = .var (.free l) ∧
        m.lookup l = some (.capability (.mcell n0 ℓ0)) ∧ Ψ l = some Tc
  | .arrow T1 _ _, k, Ψ, m, e =>
      (∃ cs0 T0 t0, resolve m.heap e = some (.abs cs0 T0 t0)) ∧
      ∀ j, j < k → ∀ (Ψ' : TWorld) (m' : Memory) (arg : Nat),
        WorldLe Ψ' m' Ψ m →
        -- inlined `MemTyped j Ψ' m'` (standalone def would be a forward reference)
        (∀ l Tc' n, Ψ' l = some Tc' →
            m'.lookup l = some (.capability (.mcell n .live)) →
            ∀ i, i < j → val_denot Tc' i Ψ' m' (.var (.free n))) →
        val_denot T1 j Ψ' m' (.var (.free arg)) →
        resolve m'.heap (.var (.free arg)) ≠ none
  | _, _, _, _, _ => True
termination_by _ k => k
decreasing_by all_goals omega

/-- **Well-typed world at index `k`** (standalone form of the inlined premise above). -/
def MemTyped (k : Nat) (Ψ : TWorld) (m : Memory) : Prop :=
  (∀ l Tc, Ψ l = some Tc → ∃ n ℓ, m.lookup l = some (.capability (.mcell n ℓ))) ∧
  ∀ l Tc n, Ψ l = some Tc → m.lookup l = some (.capability (.mcell n .live)) →
    ∀ i, i < k → val_denot Tc i Ψ m (.var (.free n))

/-! ## The keystone the flat store lacked: `WorldLe`-monotonicity -/

/-- **`WorldLe`-monotonicity.**  The value relation transports along store growth.  The `cell`
case is now *trivial* — the stored type `Tc` is persisted verbatim by `WorldLe` (contrast the
flat relation store, whose frozen `R` would have to be re-pinned to the grown world).  The
`arrow` case is monotone for free by `WorldLe.trans`.  No induction on the type is needed. -/
theorem val_denot_worldle_mono (T : Ty .capt {}) {k Ψ1 Ψ2 m1 m2} (hwle : WorldLe Ψ2 m2 Ψ1 m1)
    {e} : val_denot T k Ψ1 m1 e → val_denot T k Ψ2 m2 e := by
  cases T with
  | unit => simp only [val_denot]; exact resolve_monotonic hwle.1
  | bool =>
    simp only [val_denot]
    rintro (h | h)
    · exact Or.inl (resolve_monotonic hwle.1 h)
    · exact Or.inr (resolve_monotonic hwle.1 h)
  | cell cs Tc =>
    simp only [val_denot]
    rintro ⟨l, n0, ℓ0, he, hlk, hΨl⟩
    obtain ⟨n', ℓ', hlk'⟩ := mcell_up hwle.1 hlk
    exact ⟨l, n', ℓ', he, hlk', hwle.2 l Tc hΨl⟩
  | arrow T1 cs T2 =>
    simp only [val_denot]
    rintro ⟨⟨cs0, T0, t0, habs⟩, hbody⟩
    refine ⟨⟨cs0, T0, t0, resolve_monotonic hwle.1 habs⟩, fun j hjk Ψ' m' arg hwle' hmt harg => ?_⟩
    exact hbody j hjk Ψ' m' arg (WorldLe.trans hwle hwle') hmt harg
  | _ => simp only [val_denot]; exact id

/-- **Downward closure in the index.**  The `cell` case is index-independent; the `arrow`
case restricts `∀ j < k` to `∀ j < k'`. -/
theorem val_denot_downward {T : Ty .capt {}} {j k : Nat} (hjk : j ≤ k) {Ψ m e} :
    val_denot T k Ψ m e → val_denot T j Ψ m e := by
  cases T with
  | arrow T1 cs T2 =>
    simp only [val_denot]
    rintro ⟨habs, hbody⟩
    exact ⟨habs, fun i hij => hbody i (Nat.lt_of_lt_of_le hij hjk)⟩
  | _ => simp only [val_denot, imp_self]

/-! ## Read and write soundness -/

/-- **Read soundness.**  At a well-typed world, dereferencing a live cell yields a value of the
cell's content type at every depth `< k` — directly, since the store *is* the type. -/
theorem read_typed {k Ψ m l Tc n} (hwt : MemTyped k Ψ m) (hΨl : Ψ l = some Tc)
    (hlk : m.lookup l = some (.capability (.mcell n .live))) :
    ∀ i, i < k → val_denot Tc i Ψ m (.var (.free n)) :=
  hwt.2 l Tc n hΨl hlk

/-- **Write soundness (the crux).**  Writing a value `e_y` that is a `Tc`-value at index `k`
re-establishes the content-typing obligation at every depth `< k`.  Immediate from index
downward-closure — and, unlike the flat store, no world-stability side condition is needed,
because the cell obligation is stated by re-interpreting the *type* `Tc` at the current world. -/
theorem write_reestablishes {k Ψ Tc m_upd e_y}
    (hy : val_denot Tc k Ψ m_upd e_y) : ∀ i, i < k → val_denot Tc i Ψ m_upd e_y :=
  fun _ hik => val_denot_downward (Nat.le_of_lt hik) hy

end StepIndexedTypeStore
end CoreCapybara
