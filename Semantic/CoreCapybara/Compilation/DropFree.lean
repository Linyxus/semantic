import Semantic.CoreCapybara.Capybara.Substitution
import Semantic.CoreCapybara.Substitution
import Semantic.CoreCapybara.Compilation.TypeCompiler
import Semantic.CoreCapybara.Compilation.AppChain

/-!
# Drop-free reflection machinery

This file builds the **additive** foundation for showing that the split-covering
dispatch's `.drop` sub-branch is vacuous: the origin peak's access mode `M1 ≠ .drop`,
where `cvar M1 Z1 ⊆ compile (peaks Γorig cs) scOrig`.

Because `compile` and `peaks` preserve access modes, `M1 = .drop` iff the source
`peaks Γorig cs` carries a `.drop`-mode cvar atom.  `peaks` resolves `var` atoms
THROUGH the context (`peaksVarBound`), applying the var atom's access mode to the
resolved cvars via `applyAccess` — and `applyAccess .drop = applyDrop` overwrites
*every* atom to `.drop`.  Hence a `.drop`-mode **var** atom (not just a `.drop`
cvar) can inject `.drop`s.  Drop-freeness of `peaks Γ cs` therefore needs BOTH `cs`
drop-free AND `Γ`'s stored-type captures drop-free.

## Relation to `AccessOnly`

`CapyCaptureSet.AccessOnly Γ C := ∀ c, cvar .drop c ⊆ resourcePeaks Γ C → False` is a
DIFFERENT predicate: it is stated over the already-context-resolved RESOURCE view
`resourcePeaks Γ C`, and it only mentions `.drop`-**cvar** atoms.  It is *not* a raw
syntactic predicate on `C`, and it does not by itself see `.drop`-**var** atoms.  So
here we define a clean raw `DropFree` predicate ("no atom held at `.drop` access
mode", covering both cvar and var atoms) and reflect it through `peaks`/`compile`.
-/

namespace CoreCapybara

open Compilation

/-! ## Access helpers -/

/-- An `.M`-mode access is never `.drop`. -/
theorem Access.M_ne_drop {m : Mutability} : (Access.M m) ≠ Access.drop :=
  fun h => Access.noConfusion h

/-- `applyRO` never turns a non-`.drop` mode into `.drop` (it maps `.M _ ↦ .M .ro`
    and fixes `.drop`). -/
theorem Access.applyRO_ne_drop {a : Access} (h : a ≠ .drop) : a.applyRO ≠ .drop := by
  cases a with
  | M m => exact Access.M_ne_drop
  | drop => exact absurd rfl h

/-! ## Source-side (`CapyCaptureSet`) drop-free predicate

A capture set is `DropFree` when no atom (cvar OR var) is held at `.drop` access
mode.  Both are needed: a `.drop`-var atom injects `.drop` cvars via `peaks`. -/

inductive CapyCaptureSet.DropFree : CapyCaptureSet s → Prop where
| empty : DropFree .empty
| union {C1 C2 : CapyCaptureSet s} : DropFree C1 → DropFree C2 → DropFree (C1.union C2)
| cvar {m : Access} {c : BVar s .cvar} : m ≠ .drop → DropFree (.cvar m c)
| var {m : Access} {x : Var .var s} : m ≠ .drop → DropFree (.var m x)
| pseudo_peak {C : CapyCaptureSet s} : DropFree C → DropFree (.pseudo_peak C)

/-- `DropFree` is preserved under renaming (renaming leaves access modes untouched). -/
theorem CapyCaptureSet.DropFree.rename {cs : CapyCaptureSet s} (h : cs.DropFree)
    (ρ : Rename s s') : (cs.rename ρ).DropFree := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2
  | cvar hm => exact .cvar hm
  | var hm => exact .var hm
  | pseudo_peak _ ih => exact .pseudo_peak ih

/-- `DropFree` is preserved under `applyRO` (it maps every mode `.M _ ↦ .M .ro`). -/
theorem CapyCaptureSet.DropFree.applyRO {cs : CapyCaptureSet s} (h : cs.DropFree) :
    cs.applyRO.DropFree := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2
  | cvar hm => exact .cvar (Access.applyRO_ne_drop hm)
  | var hm => exact .var (Access.applyRO_ne_drop hm)
  | pseudo_peak _ ih => exact .pseudo_peak ih

/-- `DropFree` is preserved under `applyMut` (either the identity or `applyRO`). -/
theorem CapyCaptureSet.DropFree.applyMut {cs : CapyCaptureSet s} (h : cs.DropFree)
    {m : Mutability} : (cs.applyMut m).DropFree := by
  cases m with
  | epsilon => simpa only [CapyCaptureSet.applyMut_epsilon] using h
  | ro => simpa only [CapyCaptureSet.applyMut_ro] using h.applyRO

/-- `DropFree` is preserved under `applyAccess a` whenever `a ≠ .drop`.  (For
    `a = .drop`, `applyAccess` = `applyDrop` overwrites everything to `.drop`.) -/
theorem CapyCaptureSet.DropFree.applyAccess {cs : CapyCaptureSet s} (h : cs.DropFree)
    {a : Access} (ha : a ≠ .drop) : (cs.applyAccess a).DropFree := by
  cases a with
  | drop => exact absurd rfl ha
  | M m => simpa only [CapyCaptureSet.applyAccess_M] using h.applyMut

/-- No `.drop`-mode cvar atom is a subset of a `DropFree` source capture set. -/
theorem CapyCaptureSet.DropFree.not_drop_cvar_subset {s : Sig} {c : BVar s .cvar}
    {Y : CapyCaptureSet s} (h : Y.DropFree) : ¬ (CapyCaptureSet.cvar .drop c ⊆ Y) := by
  induction h with
  | empty => intro hsub; cases hsub
  | union _ _ ih1 ih2 =>
    intro hsub
    cases hsub with
    | union_right_left hs => exact ih1 hs
    | union_right_right hs => exact ih2 hs
  | cvar hm => intro hsub; cases hsub; exact hm rfl
  | var hm => intro hsub; cases hsub
  | pseudo_peak _ _ => intro hsub; cases hsub

/-! ## Source contexts: `StoresDropFree`

`peaks` resolves a bound var through its stored type's capture set (`peaksVarBound`),
so drop-freeness of `peaks Γ cs` needs every stored binding's captures drop-free. -/

/-- Every term-variable binding's stored type has a `DropFree` capture set. -/
def CapyCtx.StoresDropFree : CapyCtx s → Prop
| .empty => True
| .push Γ (.var T) => Γ.StoresDropFree ∧ T.captureSet.DropFree
| .push Γ (.tvar _) => Γ.StoresDropFree
| .push Γ (.cvar _ _) => Γ.StoresDropFree

/-- The tail of a `StoresDropFree` context is `StoresDropFree`. -/
theorem CapyCtx.StoresDropFree.tail {Γ : CapyCtx s} {b : CapyBinding s k}
    (h : (Γ.push b).StoresDropFree) : Γ.StoresDropFree := by
  cases b with
  | var T => exact h.1
  | tvar S => exact h
  | cvar a cb => exact h

/-! ## THE KEY REFLECTION LEMMA

`cs` drop-free + `Γ.StoresDropFree` → `(peaks Γ cs)` drop-free.  Mutual with the
`peaksVarBound` recursion, mirroring `peaks_noPseudoPeak`/`peaksVarBound_noPseudoPeak`. -/

mutual
/-- Resolving a bound var (at a non-`.drop` mode) through a `StoresDropFree` context
    yields a `DropFree` capture set. -/
theorem CapyCaptureSet.peaksVarBound_dropFree {Γ : CapyCtx s}
    (hΓ : Γ.StoresDropFree) {m : Access} (hm : m ≠ .drop) (x : BVar s .var) :
    (CapyCaptureSet.peaksVarBound Γ m x).DropFree := by
  match Γ, x, hΓ with
  | .push Γ (.var T), .here, hΓ =>
    rw [CapyCaptureSet.peaksVarBound]
    exact ((CapyCaptureSet.peaks_dropFree hΓ.1 hΓ.2).rename Rename.succ).applyAccess hm
  | .push Γ b, .there x, hΓ =>
    rw [CapyCaptureSet.peaksVarBound]
    exact (CapyCaptureSet.peaksVarBound_dropFree hΓ.tail hm x).rename Rename.succ
termination_by (sizeOf Γ, sizeOf x + 1)

/-- **Key reflection:** a drop-free capture set resolved through a `StoresDropFree`
    context is drop-free (no `.drop`-mode atom survives).  This is what the dispatch
    uses to refute `M1 = .drop`. -/
theorem CapyCaptureSet.peaks_dropFree {Γ : CapyCtx s} {cs : CapyCaptureSet s}
    (hΓ : Γ.StoresDropFree) (hcs : cs.DropFree) :
    (CapyCaptureSet.peaks Γ cs).DropFree := by
  match cs, hcs with
  | .empty, _ => rw [CapyCaptureSet.peaks]; exact DropFree.empty
  | .union cs1 cs2, .union h1 h2 =>
    rw [CapyCaptureSet.peaks]
    exact DropFree.union
      (CapyCaptureSet.peaks_dropFree hΓ h1) (CapyCaptureSet.peaks_dropFree hΓ h2)
  | .cvar m c, .cvar hm => rw [CapyCaptureSet.peaks]; exact DropFree.cvar hm
  | .var _ (.free _), _ => rw [CapyCaptureSet.peaks]; exact DropFree.empty
  | .var m (.bound x), .var hm =>
    rw [CapyCaptureSet.peaks]
    exact CapyCaptureSet.peaksVarBound_dropFree hΓ hm x
  | .pseudo_peak C, .pseudo_peak hC =>
    rw [CapyCaptureSet.peaks]
    exact DropFree.pseudo_peak (CapyCaptureSet.peaks_dropFree hΓ hC)
termination_by (sizeOf Γ, sizeOf cs)
end

/-! ## Source-side substitution preservation

A drop-free capture set substituted by a substitution whose cvar images are all
drop-free stays drop-free. -/

/-- A substitution is drop-free when every cvar image is drop-free. -/
def CapySubst.DropFree (σ : CapySubst s1 s2) : Prop := ∀ x, (σ.cvar x).DropFree

/-- Substitution preserves `DropFree` under a `DropFree` substitution. -/
theorem CapyCaptureSet.subst_dropFree {cs : CapyCaptureSet s1} {σ : CapySubst s1 s2}
    (hd : cs.DropFree) (hσ : σ.DropFree) : ((CapyCaptureSet.subst cs) σ).DropFree := by
  induction hd with
  | empty => exact .empty
  | union _ _ ih1 ih2 => simp only [CapyCaptureSet.subst]; exact .union ih1 ih2
  | @cvar m c hm => simp only [CapyCaptureSet.subst]; exact (hσ c).applyAccess hm
  | @var m x hm => simp only [CapyCaptureSet.subst]; exact .var hm
  | pseudo_peak _ ih => simp only [CapyCaptureSet.subst]; exact .pseudo_peak ih

/-- The single-`cvar` opener is drop-free when its payload is. -/
theorem CapySubst.openCVar_dropFree {C : CapyCaptureSet s} (h : C.DropFree) :
    (CapySubst.openCVar C).DropFree := by
  intro y
  cases y with
  | here => exact CapyCaptureSet.DropFree.pseudo_peak h
  | there x => exact CapyCaptureSet.DropFree.cvar Access.M_ne_drop

/-! ## Target-side (`CaptureSet`) drop-free predicate

The target calculus has no `pseudo_peak`, so the predicate is `pseudo_peak`-free. -/

inductive CaptureSet.DropFree : CaptureSet s → Prop where
| empty : DropFree .empty
| union {C1 C2 : CaptureSet s} : DropFree C1 → DropFree C2 → DropFree (C1.union C2)
| cvar {m : Access} {c : BVar s .cvar} : m ≠ .drop → DropFree (.cvar m c)
| var {m : Access} {x : Var .var s} : m ≠ .drop → DropFree (.var m x)

/-- `DropFree` is preserved under renaming. -/
theorem CaptureSet.DropFree.rename {cs : CaptureSet s} (h : cs.DropFree)
    (ρ : Rename s s') : (cs.rename ρ).DropFree := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2
  | cvar hm => exact .cvar hm
  | var hm => exact .var hm

/-- `DropFree` is preserved under `applyRO`. -/
theorem CaptureSet.DropFree.applyRO {cs : CaptureSet s} (h : cs.DropFree) :
    cs.applyRO.DropFree := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2
  | cvar hm => exact .cvar (Access.applyRO_ne_drop hm)
  | var hm => exact .var (Access.applyRO_ne_drop hm)

/-- `DropFree` is preserved under `applyMut`. -/
theorem CaptureSet.DropFree.applyMut {cs : CaptureSet s} (h : cs.DropFree)
    {m : Mutability} : (cs.applyMut m).DropFree := by
  cases m with
  | epsilon => simpa only [CaptureSet.applyMut_epsilon] using h
  | ro => simpa only [CaptureSet.applyMut_ro] using h.applyRO

/-- `DropFree` is preserved under `applyAccess a` whenever `a ≠ .drop`. -/
theorem CaptureSet.DropFree.applyAccess {cs : CaptureSet s} (h : cs.DropFree)
    {a : Access} (ha : a ≠ .drop) : (cs.applyAccess a).DropFree := by
  cases a with
  | drop => exact absurd rfl ha
  | M m => simpa only [CaptureSet.applyAccess_M] using h.applyMut

/-- **Dispatch consumer:** no `.drop`-mode cvar atom is a subset of a `DropFree`
    target capture set.  Refutes `M1 = .drop` from `cvar M1 Z1 ⊆ ⟦peaks Γ cs⟧`. -/
theorem CaptureSet.DropFree.not_drop_cvar_subset {s : Sig} {c : BVar s .cvar}
    {Y : CaptureSet s} (h : Y.DropFree) : ¬ (CaptureSet.cvar .drop c ⊆ Y) := by
  induction h with
  | empty => intro hsub; cases hsub
  | union _ _ ih1 ih2 =>
    intro hsub
    cases hsub with
    | union_right_left hs => exact ih1 hs
    | union_right_right hs => exact ih2 hs
  | cvar hm => intro hsub; cases hsub; exact hm rfl
  | var hm => intro hsub; cases hsub

/-! ## Compile preserves drop-freeness

`compile` of a raw `.var a (.bound x)` atom resolves through the target context
(`ctx.lookupVar x`), so compile-preservation is NOT unconditional.  But the object
consumed by the dispatch is `peaks Γ cs`, which is `PeaksOnly` (no var atoms) and —
over a source (`NoPseudoPeak`) context — `NoPseudoPeak`.  We therefore gate on
`PeaksOnly ∧ NoPseudoPeak`: a union-tree of cvar atoms, where `compile` only relabels
cvars and preserves their access mode. -/

/-- Compilation preserves `DropFree` for a `PeaksOnly`, `NoPseudoPeak` source set
    (`PeaksOnly` rules out the `var` lookup case, `NoPseudoPeak` the `pseudo_peak`
    descent). -/
theorem CapyCaptureSet.compile_dropFree {s1 s2 : Sig} {cs : CapyCaptureSet s1}
    {ctx : SrcCtx s1 s2}
    (hp : cs.PeaksOnly) (hnp : cs.NoPseudoPeak) (hd : cs.DropFree) :
    (CapyCaptureSet.compile cs ctx).DropFree := by
  revert hp hnp
  induction hd with
  | empty =>
    intro _ _; simp only [CapyCaptureSet.compile]; exact CaptureSet.DropFree.empty
  | union _ _ ih1 ih2 =>
    intro hp hnp
    cases hp with | union hp1 hp2 =>
    cases hnp with | union hnp1 hnp2 =>
    simp only [CapyCaptureSet.compile]
    exact CaptureSet.DropFree.union (ih1 hp1 hnp1) (ih2 hp2 hnp2)
  | cvar hm =>
    intro _ _; simp only [CapyCaptureSet.compile]; exact CaptureSet.DropFree.cvar hm
  | var _ =>
    intro hp _; nomatch hp
  | pseudo_peak _ _ =>
    intro _ hnp; nomatch hnp

/-! ## Target-side substitution / opener preservation -/

/-- A target substitution is drop-free when every cvar image is drop-free. -/
def Subst.DropFree (σ : Subst s1 s2) : Prop := ∀ x, (σ.cvar x).DropFree

/-- Substitution preserves `DropFree` under a `DropFree` substitution. -/
theorem CaptureSet.subst_dropFree {cs : CaptureSet s1} {σ : Subst s1 s2}
    (hd : cs.DropFree) (hσ : σ.DropFree) : (cs.subst σ).DropFree := by
  induction hd with
  | empty => exact .empty
  | union _ _ ih1 ih2 => simp only [CaptureSet.subst]; exact .union ih1 ih2
  | @cvar m c hm => simp only [CaptureSet.subst]; exact (hσ c).applyAccess hm
  | @var m x hm => simp only [CaptureSet.subst]; exact .var hm

/-- The single-`cvar` opener is drop-free when its payload is. -/
theorem Subst.openCVar_dropFree {C : CaptureSet s} (h : C.DropFree) :
    (Subst.openCVar C).DropFree := by
  intro y
  cases y with
  | here => exact h
  | there x => exact CaptureSet.DropFree.cvar Access.M_ne_drop

/-- The composite `appOpen` opener (c ↦ Dt, cx ↦ Cy, param ↦ yv) is drop-free when
    its two compiled capture payloads are. -/
theorem appOpen_dropFree {s : Sig} {Dt Cy : CaptureSet s} {yv : Var .var s}
    (hDt : Dt.DropFree) (hCy : Cy.DropFree) : (appOpen Dt Cy yv).DropFree := by
  intro y
  match y with
  | .there .here => exact hCy
  | .there (.there .here) => exact hDt
  | .there (.there (.there c0)) => exact CaptureSet.DropFree.cvar Access.M_ne_drop

/-! ## Composed convenience lemma for the dispatch

Directly refutes `M1 = .drop`: no `.drop`-mode cvar is a subset of the compiled
peaks of a drop-free capture set through a `StoresDropFree` (pseudo-peak-free)
context. -/

theorem CapyCaptureSet.compile_peaks_not_drop_cvar {s1 s2 : Sig}
    {Γ : CapyCtx s1} {cs : CapyCaptureSet s1} {ctx : SrcCtx s1 s2} {c : BVar s2 .cvar}
    (hΓsf : Γ.StoresDropFree) (hcssf : cs.DropFree)
    (hΓnp : Γ.NoPseudoPeak) (hcsnp : cs.NoPseudoPeak) :
    ¬ (CaptureSet.cvar .drop c ⊆
        CapyCaptureSet.compile (CapyCaptureSet.peaks Γ cs) ctx) := by
  have hpk : (CapyCaptureSet.peaks Γ cs).DropFree := CapyCaptureSet.peaks_dropFree hΓsf hcssf
  have hpo : (CapyCaptureSet.peaks Γ cs).PeaksOnly := CapyCaptureSet.peaks_peaksOnly Γ cs
  have hnp : (CapyCaptureSet.peaks Γ cs).NoPseudoPeak :=
    CapyCaptureSet.peaks_noPseudoPeak hΓnp hcsnp
  exact (CapyCaptureSet.compile_dropFree hpo hnp hpk).not_drop_cvar_subset

/-! ## Source-side TYPE drop-freeness (`CapyTy.DropFree`)

The reflection machinery above only needs a stored type's *top* capture set
(`T.captureSet`) to be `DropFree`.  For the SOURCE-SIDE ROOT THEOREM — "well-typed
source terms have drop-free types" — we need the whole *type* drop-free: every
capture set nested anywhere in the type carries no `.drop`-mode atom.  This mirrors
`CapyTy.IsClosed`/`CapyTy.NoPseudoPeak` (`Capybara/Syntax/Ty.lean`). -/

/-- A capture bound is `DropFree` when its bounding set is (an `.unbound` bound has
    no capture set, so it is vacuously drop-free). -/
inductive CapyCaptureBound.DropFree : CapyCaptureBound s → Prop where
| unbound {m : Mutability} : CapyCaptureBound.DropFree (.unbound m)
| bound {cs : CapyCaptureSet s} : cs.DropFree → CapyCaptureBound.DropFree (.bound cs)

/-- A type is `DropFree` when every capture set it mentions (latent captures, cell
    captures, sub-type captures, capture-bound bounds) is `DropFree`. -/
inductive CapyTy.DropFree : CapyTy sort s → Prop where
| top : CapyTy.DropFree .top
| tvar : CapyTy.DropFree (.tvar x)
| arrow : CapyTy.DropFree T1 → CapyCaptureSet.DropFree cs → CapyTy.DropFree T2 →
    CapyTy.DropFree (.arrow T1 cs T2)
| poly : CapyTy.DropFree T1 → CapyCaptureSet.DropFree cs → CapyTy.DropFree T2 →
    CapyTy.DropFree (.poly T1 cs T2)
| cpoly : CapyCaptureBound.DropFree cb → CapyCaptureSet.DropFree cs → CapyTy.DropFree T →
    CapyTy.DropFree (.cpoly cb cs T)
| unit : CapyTy.DropFree .unit
| cap : CapyCaptureSet.DropFree cs → CapyTy.DropFree (.cap cs)
| bool : CapyTy.DropFree .bool
| cell : CapyCaptureSet.DropFree cs → CapyTy.DropFree (.cell cs m)
| exi : CapyTy.DropFree T → CapyTy.DropFree (.exi T)
| typ : CapyTy.DropFree T → CapyTy.DropFree (.typ T)

/-- `DropFree` is preserved under renaming (renaming leaves access modes untouched). -/
theorem CapyCaptureBound.DropFree.rename {cb : CapyCaptureBound s} (h : cb.DropFree)
    (f : Rename s s') : (cb.rename f).DropFree := by
  cases h with
  | unbound => exact .unbound
  | bound hcs => exact .bound (hcs.rename f)

/-- `CapyTy.DropFree` is preserved under renaming. -/
theorem CapyTy.DropFree.rename {T : CapyTy sort s1} (h : T.DropFree) :
    ∀ {s2 : Sig} (f : Rename s1 s2), (T.rename f).DropFree := by
  induction h with
  | top => intro s2 f; exact .top
  | tvar => intro s2 f; exact .tvar
  | arrow _ hcs _ ih1 ih2 =>
    intro s2 f; simp only [CapyTy.rename]; exact .arrow (ih1 f.lift) (hcs.rename f) (ih2 f.lift)
  | poly _ hcs _ ih1 ih2 =>
    intro s2 f; simp only [CapyTy.rename]; exact .poly (ih1 f) (hcs.rename f) (ih2 f.lift)
  | cpoly hcb hcs _ ih =>
    intro s2 f; simp only [CapyTy.rename]; exact .cpoly (hcb.rename f) (hcs.rename f) (ih f.lift)
  | unit => intro s2 f; exact .unit
  | cap hcs => intro s2 f; simp only [CapyTy.rename]; exact .cap (hcs.rename f)
  | bool => intro s2 f; exact .bool
  | cell hcs => intro s2 f; simp only [CapyTy.rename]; exact .cell (hcs.rename f)
  | exi _ ih => intro s2 f; simp only [CapyTy.rename]; exact .exi (ih f.lift)
  | typ _ ih => intro s2 f; simp only [CapyTy.rename]; exact .typ (ih f)

/-- A `DropFree` capturing type has a `DropFree` (top-level) capture set. -/
theorem CapyTy.DropFree.captureSet {T : CapyTy .capt s} (h : T.DropFree) :
    T.captureSet.DropFree := by
  cases h with
  | top => exact .empty
  | tvar => exact .empty
  | arrow _ hcs _ => exact hcs
  | poly _ hcs _ => exact hcs
  | cpoly _ hcs _ => exact hcs
  | cap hcs => exact hcs
  | cell hcs => exact hcs
  | unit => exact .empty
  | bool => exact .empty

/-- Refining a `DropFree` type's capture set with a `DropFree` capture set stays
    `DropFree` (the compiler's `var`/`readonly`-style capture refinement). -/
theorem CapyTy.DropFree.refineCaptureSet {T : CapyTy .capt s} (h : T.DropFree)
    {C : CapyCaptureSet s} (hC : C.DropFree) : (T.refineCaptureSet C).DropFree := by
  cases h with
  | top => exact .top
  | tvar => exact .tvar
  | arrow hT1 _ hT2 => exact .arrow hT1 hC hT2
  | poly hT1 _ hT2 => exact .poly hT1 hC hT2
  | cpoly hcb _ hT => exact .cpoly hcb hC hT
  | cap _ => exact .cap hC
  | cell _ => exact .cell hC
  | unit => exact .unit
  | bool => exact .bool

/-! ## Source contexts: `StoresTyDropFree` (full-type version)

`CapyCtx.StoresDropFree` (above) only requires each stored binding's *capture set*
drop-free — enough for the `peaks` reflection.  The ROOT THEOREM's `var` case needs
the whole *stored type* drop-free (its result type is the stored type with a refined
capture), so we use a stronger, full-type context predicate here. -/

/-- Every term-variable binding's stored type is `DropFree` (whole type, not just its
    capture set). -/
def CapyCtx.StoresTyDropFree : CapyCtx s → Prop
| .empty => True
| .push Γ (.var T) => Γ.StoresTyDropFree ∧ T.DropFree
| .push Γ (.tvar _) => Γ.StoresTyDropFree
| .push Γ (.cvar _ _) => Γ.StoresTyDropFree

/-- The tail of a `StoresTyDropFree` context is `StoresTyDropFree`. -/
theorem CapyCtx.StoresTyDropFree.tail {Γ : CapyCtx s} {b : CapyBinding s k}
    (h : (Γ.push b).StoresTyDropFree) : Γ.StoresTyDropFree := by
  cases b with
  | var T => exact h.1
  | tvar S => exact h
  | cvar a cb => exact h

/-- `StoresTyDropFree` (full type) implies the existing `StoresDropFree` (capture set),
    since a drop-free type has a drop-free capture set. -/
theorem CapyCtx.StoresTyDropFree.toStoresDropFree {Γ : CapyCtx s}
    (h : Γ.StoresTyDropFree) : Γ.StoresDropFree := by
  induction Γ with
  | empty => exact True.intro
  | push Γ b ih =>
    cases b with
    | var T => exact ⟨ih h.1, h.2.captureSet⟩
    | tvar S => exact ih h
    | cvar a cb => exact ih h

/-! ## THE ROOT THEOREM — and its REFUTATION

The intended source-side root theorem is

```
theorem CapyHasType.dropFree {Cs Γ e E}
    (hΓ : Γ.StoresTyDropFree) (hty : CapyHasType Cs Γ e E) : E.DropFree
```

i.e. "in a well-typed source term, the term's type carries only drop-free captures".
The motivating intuition (see this file's header) is that `.drop` access lives only
in a term's *effect* capture `Cs`, never in *type annotations*.

**This intuition is FALSE in this calculus, and the theorem does not hold.**  The
`.drop`-carrying effect of a computation flows into a *type annotation* through the
**latent capture** of a function type, in two independent ways:

1. **Subsumption (`CapySubtyp.arrow` via `CapySubcapt.sc_elem`).**  Because `{} ⊆ C`
   for *any* `C` (`CapyCaptureSet.Subset.empty`), we have `CapySubcapt Γ {} {drop w}`,
   and arrow subtyping is covariant in the latent capture.  So a drop-free function
   type `Unit ->{} Unit` is a subtype of the drop-carrying `Unit ->{drop w} Unit`, and
   the `subtyp` typing rule re-types any term of the former at the latter.  This is
   `CapyTy.dropFree_not_subtyp_stable` below — a machine-checked witness that
   `CapyTy.DropFree` is NOT preserved by `CapySubtyp`, so the `subtyp` case of the
   induction is unclosable.

2. **Closure introduction (`abs`/`tabs`/`cabs`).**  The `abs` rule sets the arrow's
   latent capture `cs` equal to (the outer part of) the body's *effect*:
   the body is typed at effect `(cs.rename succ.succ) ∪ {ε here}`.  A closure whose
   body drops a *captured* (outer, droppable) resource has a `.drop`-mode atom in its
   effect on that captured variable, and — since no `CapySubcapt` step can remove a
   `.drop` (drop is order-incomparable to every `.M m`, `Access.Le`) — that `.drop`
   atom is forced into `cs`.  Concretely, `let z = alloc b in (\x. drop z)` is
   well-typed with arrow type `Unit ->{drop z} Unit`, whose latent `{drop z}` is not
   drop-free.  `tabs`/`cabs` embed the body effect into a `poly`/`cpoly` latent the
   same way.

Consequences for the downstream plan: `CapyCtx.StoresDropFree`/`StoresTyDropFree` are
NOT invariants of arbitrary well-typed source terms — a `letin` binding a
drop-in-latent closure stores a type whose capture set carries `.drop`.  Establishing
the compiler's drop-freeness obligations therefore requires an ADDED well-formedness
restriction (e.g. "arrow/poly/cpoly latents are access-only", excluding closures that
drop captured resources), which is a genuine language restriction, not mere hygiene.
Per project discipline, we do NOT force the false theorem with a `sorry`. -/

/-- **Machine-checked counterexample:** `CapyTy.DropFree` is NOT stable under
    `CapySubtyp`.  A drop-free arrow type is a subtype of a drop-carrying arrow type
    (latent-capture covariance + `{} ⊆ {drop w}`), so the `subtyp` typing rule breaks
    drop-freeness of the term's type.  This refutes the naive `CapyHasType.dropFree`
    (see the note above). -/
theorem CapyTy.dropFree_not_subtyp_stable {s : Sig} (Γ : CapyCtx s) (w : BVar s .var) :
    CapySubtyp Γ
      (.arrow (.unit) (.empty) (.typ .unit))
      (.arrow (.unit) (.var .drop (.bound w)) (.typ .unit))
    ∧ (CapyTy.arrow (.unit) (.empty) (.typ .unit) : CapyTy .capt s).DropFree
    ∧ ¬ (CapyTy.arrow (.unit) (.var .drop (.bound w)) (.typ .unit) : CapyTy .capt s).DropFree := by
  refine ⟨?_, ?_, ?_⟩
  · -- `Unit ->{} Unit  <:  Unit ->{drop w} Unit` : latent-capture covariance.
    apply CapySubtyp.arrow
    · exact CapySubcapt.sc_elem CapyCaptureSet.Subset.empty
    · exact CapySubtyp.refl
  · -- the subtype is drop-free.
    exact CapyTy.DropFree.arrow CapyTy.DropFree.unit CapyCaptureSet.DropFree.empty
      (CapyTy.DropFree.typ CapyTy.DropFree.unit)
  · -- the supertype is NOT drop-free: its latent `.var .drop w` is a `.drop` atom.
    intro h
    cases h with
    | arrow _ hcs _ => cases hcs with | var hm => exact hm rfl

end CoreCapybara
