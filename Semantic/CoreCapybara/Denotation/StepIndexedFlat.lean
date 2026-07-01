import Semantic.CoreCapybara.Semantics.Heap

/-!
# Flat, truncation-based step-indexed store world (sandbox)

Validating the CORRECT keystone before promoting into `KripkeModel.lean`.

The dependent `World : Nat → Type` family with a content-fabricating `extend`
(prototype `StepIndexedProto.lean`) cannot satisfy the naive coherence
`val_denot T (n+1) (extend w) ↔ val_denot T n w`: `extend`'s canonical padding at the
bottom level would have to be simultaneously `True` (to match a cell's agreement clause)
and structural (to match e.g. `unit`), which is impossible.  See the note in the roadmap.

The elegant, standard (Ahmed-style) fix keeps the world **flat** and stratifies with an
**index truncation** `approx k` instead of a dependent world tower:

* a store typing `SWorld` maps a location to a *step-indexed* relation `SRel`;
* the cell relation compares the stored relation with `val_denot Tc` only at indices
  `j < k`, so the comparison is trivial at the boundary `k = 0` (no fabricated content);
* `val_denot` is well-founded by recursion on the index `k` alone (every recursive call is
  at a strictly smaller `j < k`), so it stays a plain Lean definition;
* the keystone is **non-expansiveness**: `val_denot T k Ψ` depends only on `Ψ.approx k`.
  Downward closure in the index is then immediate (`∀ j < k` restricts to `∀ j < k'`).
-/

namespace CoreCapybara
namespace StepIndexedFlat

/-- A **step-indexed relation**: for each observation depth `j`, a memory–expression
predicate.  Intended to be downward-closed in `j`. -/
abbrev SRel : Type := Nat → Memory → Exp {} → Prop

/-- A **flat store typing / world**: assigns each mutable location a step-indexed relation.
No dependent tower — the stratification lives in the index of `SRel`, not in the type. -/
abbrev SWorld : Type := Nat → Option SRel

/-- Truncate a relation to depths `< k`. -/
def SRel.approx (k : Nat) (R : SRel) : SRel := fun j m e => j < k ∧ R j m e

/-- Truncate every stored relation of a world to depths `< k`. -/
def SWorld.approx (k : Nat) (Ψ : SWorld) : SWorld := fun l => (Ψ l).map (SRel.approx k)

/-- **The flat step-indexed value relation.**  Recursion is well-founded on the index `k`:
the `cell` case consults the stored relation and `val_denot Tc` only at `j < k`. -/
def val_denot : Ty .capt {} → Nat → SWorld → Memory → Exp {} → Prop
  | .unit, _, _, m, e => resolve m.heap e = some .unit
  | .bool, _, _, m, e => resolve m.heap e = some .btrue ∨ resolve m.heap e = some .bfalse
  | .cell _ Tc, k, Ψ, m, e =>
      ∃ l n0 ℓ0 R, e = .var (.free l) ∧
        m.lookup l = some (.capability (.mcell n0 ℓ0)) ∧
        Ψ l = some R ∧
        ∀ j, j < k → ∀ m' e', R j m' e' ↔ val_denot Tc j Ψ m' e'
  | .arrow T1 _ _, k, Ψ, m, e =>
      -- Toy higher-order case: `e` is an abstraction, and at every strictly smaller index
      -- its behaviour is constrained through the *domain* denotation `val_denot T1 j Ψ`
      -- (the existential codomain is Phase-3 machinery, modeled here by the domain, as in
      -- `KripkeModel.kdenot`).  This is genuinely world- and index-dependent — enough to
      -- exercise the keystone (non-expansiveness recursion + index downward-closure) for a
      -- cell whose content is a function.
      (∃ cs0 T0 t0, resolve m.heap e = some (.abs cs0 T0 t0)) ∧
      ∀ j, j < k → ∀ (m' : Memory) (arg : Nat),
        m'.subsumes m → val_denot T1 j Ψ m' (.var (.free arg)) →
        resolve m'.heap (.var (.free arg)) ≠ none
  | _, _, _, _, _ => True
termination_by _ k => k
decreasing_by all_goals omega

/-! ## `approx` algebra -/

/-- Truncating to `< j` after truncating to `< k` is truncating to `< j` (for `j ≤ k`). -/
theorem SRel.approx_approx {j k : Nat} (hjk : j ≤ k) (R : SRel) :
    SRel.approx j (SRel.approx k R) = SRel.approx j R := by
  funext i m e
  simp only [SRel.approx]
  apply propext
  constructor
  · rintro ⟨hij, _, hR⟩; exact ⟨hij, hR⟩
  · rintro ⟨hij, hR⟩; exact ⟨hij, Nat.lt_of_lt_of_le hij hjk, hR⟩

theorem SWorld.approx_approx {j k : Nat} (hjk : j ≤ k) (Ψ : SWorld) :
    (Ψ.approx k).approx j = Ψ.approx j := by
  funext l
  simp only [SWorld.approx, Option.map_map]
  cases Ψ l with
  | none => rfl
  | some R => simp only [Option.map_some, Function.comp_apply, SRel.approx_approx hjk]

/-- World-agreement below `k` propagates down to any `j ≤ k`. -/
theorem SWorld.approx_le {j k : Nat} (hjk : j ≤ k) {Ψ Ψ' : SWorld}
    (h : Ψ.approx k = Ψ'.approx k) : Ψ.approx j = Ψ'.approx j := by
  rw [← SWorld.approx_approx hjk Ψ, ← SWorld.approx_approx hjk Ψ', h]

/-- From world-agreement below `k`, a location typed in `Ψ` is typed in `Ψ'` by a relation
that agrees with it below `k`. -/
theorem SWorld.approx_lookup {k l : Nat} {Ψ Ψ' : SWorld} (h : Ψ.approx k = Ψ'.approx k)
    {R : SRel} (hR : Ψ l = some R) :
    ∃ R', Ψ' l = some R' ∧ SRel.approx k R' = SRel.approx k R := by
  have hcong := congrFun h l
  simp only [SWorld.approx, hR, Option.map_some] at hcong
  cases hΨ'l : Ψ' l with
  | none => rw [hΨ'l, Option.map_none] at hcong; exact absurd hcong (Option.some_ne_none _)
  | some R' =>
    rw [hΨ'l] at hcong
    simp only [Option.map_some, Option.some.injEq] at hcong
    exact ⟨R', rfl, hcong.symm⟩

/-- Two relations that agree below `k` are equivalent at every `j < k`. -/
theorem SRel.approx_agree {j k : Nat} (hjk : j < k) {R R' : SRel}
    (h : SRel.approx k R = SRel.approx k R') (m e) : R j m e ↔ R' j m e := by
  have hcong := congrFun (congrFun (congrFun h j) m) e
  simp only [SRel.approx, eq_iff_iff] at hcong
  exact ⟨fun hr => (hcong.mp ⟨hjk, hr⟩).2, fun hr => (hcong.mpr ⟨hjk, hr⟩).2⟩

/-! ## Downward closure in the index -/

/-- **Downward closure in the index.**  Immediate: the `cell` case's `∀ i < k` restricts to
`∀ i < j`; base cases are index-independent.  No recursion on the type is needed. -/
theorem val_denot_downward {T : Ty .capt {}} {j k : Nat} (hjk : j ≤ k) {Ψ m e} :
    val_denot T k Ψ m e → val_denot T j Ψ m e := by
  cases T with
  | cell cs Tc =>
    simp only [val_denot]
    rintro ⟨l, n0, ℓ0, R, he, hlk, hΨl, hag⟩
    exact ⟨l, n0, ℓ0, R, he, hlk, hΨl, fun i hij => hag i (Nat.lt_of_lt_of_le hij hjk)⟩
  | arrow T1 cs T2 =>
    simp only [val_denot]
    rintro ⟨habs, hbody⟩
    exact ⟨habs, fun i hij => hbody i (Nat.lt_of_lt_of_le hij hjk)⟩
  | _ => simp only [val_denot, imp_self]

/-! ## The keystone: non-expansiveness -/

/-- **Non-expansiveness (the keystone).**  `val_denot T k` depends only on the world's
`k`-approximation.  Proved by strong induction on the index: the `cell` case consults the
stored relation and `val_denot Tc` only at `j < k`, and world-agreement below `k` implies
agreement below `j` (`approx_le`), so the induction hypothesis applies. -/
theorem val_denot_nonexpansive (T : Ty .capt {}) (k : Nat) {Ψ Ψ' : SWorld}
    (hΨ : Ψ.approx k = Ψ'.approx k) (m e) :
    val_denot T k Ψ m e ↔ val_denot T k Ψ' m e := by
  induction k using Nat.strong_induction_on generalizing T Ψ Ψ' m e with
  | _ k IH =>
    cases T with
    | cell cs Tc =>
      simp only [val_denot]
      constructor
      · rintro ⟨l, n0, ℓ0, R, he, hlk, hΨl, hag⟩
        obtain ⟨R', hΨ'l, hRR'⟩ := SWorld.approx_lookup hΨ hΨl
        refine ⟨l, n0, ℓ0, R', he, hlk, hΨ'l, fun j hjk m' e' => ?_⟩
        rw [SRel.approx_agree hjk hRR' m' e', hag j hjk m' e',
          IH j hjk Tc (SWorld.approx_le (Nat.le_of_lt hjk) hΨ) m' e']
      · rintro ⟨l, n0, ℓ0, R', he, hlk, hΨ'l, hag⟩
        obtain ⟨R, hΨl, hRR'⟩ := SWorld.approx_lookup hΨ.symm hΨ'l
        refine ⟨l, n0, ℓ0, R, he, hlk, hΨl, fun j hjk m' e' => ?_⟩
        rw [SRel.approx_agree hjk hRR' m' e', hag j hjk m' e',
          IH j hjk Tc (SWorld.approx_le (Nat.le_of_lt hjk) hΨ) m' e']
    | arrow T1 cs T2 =>
      simp only [val_denot]
      constructor
      · rintro ⟨habs, hbody⟩
        refine ⟨habs, fun j hjk m' arg hsub harg => ?_⟩
        exact hbody j hjk m' arg hsub
          ((IH j hjk T1 (SWorld.approx_le (Nat.le_of_lt hjk) hΨ) m' _).mpr harg)
      · rintro ⟨habs, hbody⟩
        refine ⟨habs, fun j hjk m' arg hsub harg => ?_⟩
        exact hbody j hjk m' arg hsub
          ((IH j hjk T1 (SWorld.approx_le (Nat.le_of_lt hjk) hΨ) m' _).mp harg)
    | _ => simp only [val_denot]

/-! ## Worlds, well-typedness, and the structural lemmas -/

/-- A mutable cell present in `m1` is present (as a mutable cell) in any subsuming `m2`. -/
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

/-- **The typed future-world relation.**  The memory grows (`subsumes`) and the store typing
only grows (existing cells keep their assigned relation). -/
def WorldLe (Ψ' : SWorld) (m' : Memory) (Ψ : SWorld) (m : Memory) : Prop :=
  m'.subsumes m ∧ ∀ l R, Ψ l = some R → Ψ' l = some R

theorem WorldLe.refl (Ψ : SWorld) (m : Memory) : WorldLe Ψ m Ψ m :=
  ⟨Memory.subsumes_refl m, fun _ _ h => h⟩

theorem WorldLe.trans {Ψ1 Ψ2 Ψ3 m1 m2 m3} (h12 : WorldLe Ψ2 m2 Ψ1 m1)
    (h23 : WorldLe Ψ3 m3 Ψ2 m2) : WorldLe Ψ3 m3 Ψ1 m1 :=
  ⟨Memory.subsumes_trans h23.1 h12.1, fun l R h => h23.2 l R (h12.2 l R h)⟩

/-- Memory-growth component of `WorldLe`. -/
theorem WorldLe.subsumes {Ψ' m' Ψ m} (h : WorldLe Ψ' m' Ψ m) : m'.subsumes m := h.1

/-- Store-typing persistence: a location typed in `Ψ` keeps its relation in any future `Ψ'`. -/
theorem WorldLe.lookup {Ψ' m' Ψ m l R} (h : WorldLe Ψ' m' Ψ m) (hR : Ψ l = some R) :
    Ψ' l = some R := h.2 l R hR

/-- Store consistency: every typed location is an allocated mutable cell. -/
def StoreConsistent (Ψ : SWorld) (m : Memory) : Prop :=
  ∀ l R, Ψ l = some R → ∃ n ℓ, m.lookup l = some (.capability (.mcell n ℓ))

/-- **Well-typed world at index `k`.**  Every live mutable cell's content satisfies its
stored relation at every observation depth `< k`. -/
def MemTyped (k : Nat) (Ψ : SWorld) (m : Memory) : Prop :=
  StoreConsistent Ψ m ∧
  ∀ l R n, Ψ l = some R → m.lookup l = some (.capability (.mcell n .live)) →
    ∀ j, j < k → R j m (.var (.free n))

/-- Well-typedness is downward-closed in the index. -/
theorem MemTyped.downward {j k Ψ m} (hjk : j ≤ k) (h : MemTyped k Ψ m) : MemTyped j Ψ m :=
  ⟨h.1, fun l R n hΨ hlk i hij => h.2 l R n hΨ hlk i (Nat.lt_of_lt_of_le hij hjk)⟩

/-! ## Memory-monotonicity of the value relation -/

/-- `val_denot` transports along memory growth (`subsumes`) at a fixed world/index.  The
`cell` agreement clause is memory-independent; the `arrow` body only weakens its `subsumes`
premise. -/
theorem val_denot_mem_mono (T : Ty .capt {}) {k Ψ m m2 e} (hsub : m2.subsumes m) :
    val_denot T k Ψ m e → val_denot T k Ψ m2 e := by
  cases T with
  | unit => simp only [val_denot]; exact resolve_monotonic hsub
  | bool =>
    simp only [val_denot]
    rintro (h | h)
    · exact Or.inl (resolve_monotonic hsub h)
    · exact Or.inr (resolve_monotonic hsub h)
  | cell cs Tc =>
    simp only [val_denot]
    rintro ⟨l, n0, ℓ0, R, he, hlk, hΨl, hag⟩
    obtain ⟨n', ℓ', hlk'⟩ := mcell_up hsub hlk
    exact ⟨l, n', ℓ', R, he, hlk', hΨl, hag⟩
  | arrow T1 cs T2 =>
    simp only [val_denot]
    rintro ⟨⟨cs0, T0, t0, habs⟩, hbody⟩
    refine ⟨⟨cs0, T0, t0, resolve_monotonic hsub habs⟩, fun j hjk m' arg hsub' harg => ?_⟩
    exact hbody j hjk m' arg (Memory.subsumes_trans hsub' hsub) harg
  | _ => simp only [val_denot]; exact id

/-! ## Read and write soundness (the payoff)

Both directions of the cell's stored relation are available, because the cell agreement is a
biconditional `R j ↔ val_denot Tc j` (below `k`).  Read uses the forward direction; write
uses the backward one — the direction the frozen `MonRel` model could not supply. -/

/-- **Read soundness.**  At a well-typed world, dereferencing a live cell `l` (whose stored
relation `R` agrees with `val_denot Tc` below `k`) yields a `Tc`-value at every depth `< k`. -/
theorem read_typed {k Ψ m l R n Tc} (hwt : MemTyped k Ψ m) (hΨl : Ψ l = some R)
    (hlk : m.lookup l = some (.capability (.mcell n .live)))
    (hag : ∀ j, j < k → ∀ m' e', R j m' e' ↔ val_denot Tc j Ψ m' e') :
    ∀ j, j < k → val_denot Tc j Ψ m (.var (.free n)) :=
  fun j hjk => (hag j hjk m (.var (.free n))).mp (hwt.2 l R n hΨl hlk j hjk)

/-- **Write soundness (the crux).**  Given the cell's biconditional agreement and a value
`e_y` that is a `Tc`-value at index `k` and the (updated) world, the stored relation `R`
holds of `e_y` at every depth `< k` — the BACKWARD direction the frozen `MonRel` model could
not supply.  Immediate from the biconditional + index downward-closure. -/
theorem write_reestablishes {k : Nat} {Ψ : SWorld} {Tc : Ty .capt {}} {R : SRel}
    {m_upd : Memory} {e_y : Exp {}}
    (hag : ∀ j, j < k → ∀ m' e', R j m' e' ↔ val_denot Tc j Ψ m' e')
    (hy : val_denot Tc k Ψ m_upd e_y) :
    ∀ j, j < k → R j m_upd e_y :=
  fun j hjk => (hag j hjk m_upd e_y).mpr (val_denot_downward (Nat.le_of_lt hjk) hy)

/-! ## End-to-end toy validation

The two intended toy shapes go through the SAME generic soundness lemmas — the keystone
handles the higher-order (cell-of-arrow) case with no extra machinery. -/

/-- Base cell (`Tc = unit`): writing a `unit` value re-establishes the stored relation. -/
example {k : Nat} {Ψ : SWorld} {R : SRel} {m_upd : Memory} {e_y : Exp {}}
    (hag : ∀ j, j < k → ∀ m' e', R j m' e' ↔ val_denot .unit j Ψ m' e')
    (hy : val_denot .unit k Ψ m_upd e_y) : ∀ j, j < k → R j m_upd e_y :=
  write_reestablishes hag hy

/-- Cell-of-arrow (higher-order store): writing a function value re-establishes the stored
relation through the very same lemma. -/
example {k : Nat} {Ψ : SWorld} {R : SRel} {m_upd : Memory} {e_y : Exp {}}
    {Tf : Ty .capt {}} (_hTf : ∃ T1 cs T2, Tf = Ty.arrow T1 cs T2)
    (hag : ∀ j, j < k → ∀ m' e', R j m' e' ↔ val_denot Tf j Ψ m' e')
    (hy : val_denot Tf k Ψ m_upd e_y) : ∀ j, j < k → R j m_upd e_y :=
  write_reestablishes hag hy

-- Verified sorryAx-free: `#print axioms val_denot_nonexpansive` / `read_typed` /
-- `write_reestablishes` all report only `[propext, Quot.sound]` — no `sorryAx`, not even
-- `Classical.choice`.

end StepIndexedFlat
end CoreCapybara
