import Semantic.CoreCapybara.LegacyCompilation.CompilerCtx
open CoreCapybara
namespace Compilation

/-- Compiles a source capture set into the target -/
def CapyCaptureSet.compile : CapyCaptureSet s1 -> SrcCtx s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, ctx => .union (CapyCaptureSet.compile cs1 ctx) (CapyCaptureSet.compile cs2 ctx)
| .cvar a c, ctx => .cvar a (ctx.lookupCVar c)
| .var a (.bound x), ctx => (ctx.lookupVar x).applyAccess a
| .var a (.free n), _ => .var a (.free n)
-- In ORDINARY (non-lock) capture positions a `pseudo_peak C` is just its content:
-- it compiles transparently to `⟦C⟧`.  (The freeze is only observed by the lock
-- machinery — `peakCvars`/`peakItem`/`peakSepCtx` — which keeps a `pseudo_peak` as a
-- single grouped item; see the `peakCvars`/`accessedAt` arms below.)  Transparency
-- here is what makes the compile bridge `⟦cs[openCVar D]⟧ = ⟦cs⟧[openCVar ⟦D⟧]` hold
-- now that `openCVar` introduces `pseudo_peak`s live.
| .pseudo_peak C, ctx => CapyCaptureSet.compile C ctx

/-- Compiles a source capture bound into the target.  The mutability annotation
    on an `unbound` source bound has no counterpart in Core's nullary `.unbound`,
    so it is dropped here and recovered separately in the lock of a compiled
    capture-polymorphic function (see `CapyCaptureBound.mutabilityCtx`). -/
def CapyCaptureBound.compile : CapyCaptureBound s1 -> SrcCtx s1 s2 -> CaptureBound s2
| .unbound _, _ => .unbound
| .bound cs, ctx => .bound (CapyCaptureSet.compile cs ctx)

/-- The mutability obligation a capture bound imposes on its bound variable `c`.
    An `unbound m` bound fixes `c`'s mutability to `m` explicitly (so we record
    `{c}` at kind `m`); a `.bound` bound constrains `c` only through its capture
    set and imposes no direct mutability. -/
def CapyCaptureBound.mutabilityCtx :
    CapyCaptureBound s1 -> BVar s2 .cvar -> MutabilityCtx s2
| .unbound m, c => .cons .empty (.cvar (.M .epsilon) c) m
| .bound _, _ => .empty

/-- Source and target type-sorts coincide; this maps between the two enums. -/
def CapyTySort.compile : CapyTySort -> TySort
| .capt => .capt
| .exi => .exi

/-- Decidable equality on de Bruijn variables (the indexed `BVar` derives none). -/
def BVar.decEq : (x y : BVar s k) -> Decidable (x = y)
| .here, .here => isTrue rfl
| .here, .there _ => isFalse (by intro h; cases h)
| .there _, .here => isFalse (by intro h; cases h)
| .there x, .there y =>
  match BVar.decEq x y with
  | isTrue h => isTrue (by rw [h])
  | isFalse h => isFalse (by simp only [BVar.there.injEq]; exact h)

instance : DecidableEq (BVar s k) := BVar.decEq

deriving instance DecidableEq for Mutability
deriving instance DecidableEq for Access
deriving instance DecidableEq for Var
deriving instance DecidableEq for CapyCaptureSet

/-- De-duplicates a list (keeping the first occurrence of each element). -/
def dedup [DecidableEq α] : List α -> List α
| [] => []
| a :: as => let d := dedup as; if a ∈ d then d else a :: d

/-- The de-duplicated capture variables of a peak set, with access modes
    discarded. -/
def peakCvars (P : CapyPeakSet s) : List (BVar s .cvar) :=
  dedup (go P.cs)
where
  go : CapyCaptureSet s -> List (BVar s .cvar)
  | .empty => []
  | .union c1 c2 => go c1 ++ go c2
  | .cvar _ c => [c]
  | .var _ _ => []
  -- PLACEHOLDER (see `CapyCaptureSet.compile`): a pseudo-peak is invisible to the
  -- lock machinery for now (contributes no peak cvars).
  | .pseudo_peak _ => []

/-- The access modes at which a given capture variable is accessed in a peak
    set. -/
def accessedAt (P : CapyPeakSet s) (c : BVar s .cvar) : List Access :=
  go P.cs
where
  go : CapyCaptureSet s -> List Access
  | .empty => []
  | .union c1 c2 => go c1 ++ go c2
  | .cvar a c' => if c' = c then [a] else []
  | .var _ _ => []
  -- PLACEHOLDER (see `CapyCaptureSet.compile`): a pseudo-peak is invisible to the
  -- lock machinery for now (records no access modes).
  | .pseudo_peak _ => []

/-- The capture set holding all access-mode occurrences of a single peak `c` in a
    peak set, e.g. `{.ro c, .drop c}`. -/
def peakItem (P : CapyPeakSet s) (c : BVar s .cvar) : CapyCaptureSet s :=
  (accessedAt P c).foldr (fun a acc => (.cvar a c) ∪ acc) .empty

/-- The de-duplicated mode-erased *bases* of the frozen peaks in a peak set.  A
    `pseudo_peak C` contributes its base `C.modeErase`; two frozen-peak occurrences
    that differ only by a substitution-folded access mode share a base, so they
    group into a single lock item (cf. `peakCvars` for ordinary peaks). -/
def peakPseudos (P : CapyPeakSet s) : List (CapyCaptureSet s) :=
  dedup (go P.cs)
where
  go : CapyCaptureSet s -> List (CapyCaptureSet s)
  | .empty => []
  | .union c1 c2 => go c1 ++ go c2
  | .cvar _ _ => []
  | .var _ _ => []
  | .pseudo_peak C => [C.modeErase]

/-- The capture set holding all frozen-peak occurrences sharing a mode-erased base
    `D` in a peak set: their union, kept as `pseudo_peak` atoms (so `compile`
    transparency unfolds each to its content `⟦C⟧`). -/
def pseudoItem (P : CapyPeakSet s) (D : CapyCaptureSet s) : CapyCaptureSet s :=
  go P.cs
where
  go : CapyCaptureSet s -> CapyCaptureSet s
  | .empty => .empty
  | .union c1 c2 => (go c1) ∪ (go c2)
  | .cvar _ _ => .empty
  | .var _ _ => .empty
  | .pseudo_peak C => if C.modeErase = D then .pseudo_peak C else .empty

/-- A **peak** of a peak set: either an ordinary capture variable (`cvar`) or a
    frozen `pseudo_peak` base (`pseudo`).  These are the keys of the compiled lock:
    one separation item per distinct peak. -/
inductive Peak (s : Sig) where
| cvar : BVar s .cvar → Peak s
| pseudo : CapyCaptureSet s → Peak s
deriving DecidableEq

/-- Renames a peak through a source renaming (cvar peaks via `fs.var`, frozen-peak
    bases via capture-set renaming). -/
def Peak.rename : Peak s1 → Rename s1 s2 → Peak s2
| .cvar c, fs => .cvar (fs.var c)
| .pseudo D, fs => .pseudo (D.rename fs)

/-- The source capture set a peak contributes to the lock: `peakItem` for a cvar
    peak (its access-mode occurrences), `pseudoItem` for a frozen-peak base (its
    occurrences sharing that mode-erased base). -/
def peakKeyItem (P : CapyPeakSet s) : Peak s → CapyCaptureSet s
| .cvar c => peakItem P c
| .pseudo D => pseudoItem P D

/-- The distinct peaks of a peak set: the cvar peaks first, then the frozen-peak
    bases.  Keeping a frozen peak as its own peak — distinct from any cvar peak — is
    exactly what stops capture substitution from merging two distinct origin peaks
    (the B2c lock-stability device). -/
def peakList (P : CapyPeakSet s) : List (Peak s) :=
  (peakCvars P).map Peak.cvar ++ (peakPseudos P).map Peak.pseudo

/-- A peak is **stable** in `Γ` when `CapySubcapt` can never dissolve it: a `cvar`
    peak is stable iff its cvar is (`CapyCtx.IsStableCVar`); a `pseudo` (frozen)
    peak is always stable, since `CapySubcapt` has no rule descending into a
    `pseudo_peak`.  Only stability-restricted separation claims survive capture-set
    subtyping — see `CapyCtx.peaks_subcapt_stable_subset`. -/
def Peak.IsStable (Γ : CapyCtx s) : Peak s → Prop
| .cvar c => Γ.IsStableCVar c
| .pseudo _ => True

instance Peak.IsStable.decidable (Γ : CapyCtx s) (p : Peak s) : Decidable (Peak.IsStable Γ p) :=
  match p with
  | .cvar c => CapyCtx.IsStableCVar.decidable Γ c
  | .pseudo _ => isTrue trivial

/-- The separation context of a peak set: one item per distinct **stable** peak,
    compiled into the target.  Distinct stable peaks become distinct items and are
    therefore required to be pairwise separate; unstable peaks (`.access_only` cvars
    with a `.bound` — the ones `CapySubcapt.sc_cvar` can dissolve into a different
    capture set) are dropped, since their separation would not survive capture-set
    subtyping (`CapySubtyp.compile`'s arrow/poly/cpoly cases). -/
def peakSepCtx (Γ : CapyCtx s1) (P : CapyPeakSet s1) (ctx : SrcCtx s1 s2) : SepCtx s2 :=
  ((peakList P).filter (fun p => decide (Peak.IsStable Γ p))).foldl
    (fun K p => .cons K (CapyCaptureSet.compile (peakKeyItem P p) ctx))
    (.empty : SepCtx s2)

/-- A structural size on source types that ignores capture sets and bound
    variables.  Renaming and capture-set refinement preserve it, which justifies
    the well-founded recursion of `CapyTy.compile` over a *refined, lifted* domain
    type (which is not a syntactic subterm). -/
def tySize : CapyTy sort s -> Nat
| .top => 1
| .tvar _ => 1
| .cap _ => 1
| .cell _ _ => 1
| .unit => 1
| .bool => 1
| .arrow T _ E => 1 + tySize T + tySize E
| .poly S _ E => 1 + tySize S + tySize E
| .cpoly _ _ E => 1 + tySize E
| .exi T => 1 + tySize T
| .typ T => 1 + tySize T

@[simp] theorem tySize_rename {T : CapyTy sort s1} {f : Rename s1 s2} :
    tySize (T.rename f) = tySize T := by
  induction T generalizing s2 <;> simp_all [CapyTy.rename, tySize]

@[simp] theorem tySize_refineCaptureSet {T : CapyTy .capt s} {cs : CapyCaptureSet s} :
    tySize (T.refineCaptureSet cs) = tySize T := by
  cases T <;> simp [CapyTy.refineCaptureSet, tySize]

/-- Compiles a source type into the target signature.  The `CompilerCtx` carries
    both the source typing context (`capyCtx`, used to resolve *surface* peaks)
    and the source→target map (`srcCtx`, used to compile capture sets and look up
    variable images). -/
def CapyTy.compile : CapyTy sort s1 -> CompilerCtx s1 s2 -> Ty (CapyTySort.compile sort) s2
-- trivial / structural cases
| .top, _ => .top
| .unit, _ => .unit
| .bool, _ => .bool
| .cap cs, ctx => .cap (CapyCaptureSet.compile cs ctx.srcCtx)
| .cell cs .epsilon, ctx =>
  .cell (CapyCaptureSet.compile cs ctx.srcCtx)
| .cell cs .ro, ctx =>
  .reader (CapyCaptureSet.compile cs ctx.srcCtx)
| .typ T, ctx => .typ (CapyTy.compile T ctx)
| .tvar X, ctx => .tvar (ctx.srcCtx.lookupTVar X)
| .arrow T cs E, ctx =>
  -- `[c](x: S^C) ->cs E`  ↦  `[c][cx <: ⟦C⟧](x: S^{cx}) -> [Ψ]⟦cs ∪ {x}⟧ E`.
  let ctxB : CompilerCtx (s1,C) (s2,C)       :=
    ctx.weakenTarget.consCVar (.unbound .epsilon) .here
  -- the domain: binds `c` then `x`, mapping the value parameter `x` to its
  -- re-abstracted capture `{cx}`.  We refine the source domain `S^C` to its
  -- self-capture `S^{x}` and compile *that* (so `x ↦ cx` flows through), rather
  -- than compiling `S^C` and overwriting the result's capture set.
  let ctxDomain : CompilerCtx (s1,C,x) (s2,C,C) :=
    (ctx.weakenTarget.weakenTarget.consCVar (.unbound .epsilon) (.there .here)).consVar
      T none (.cvar (.M .epsilon) .here)
  -- the codomain AND the lock share one context: binds `c` then `x` (mapping `x`
  -- to `{cx}`), with `x` bound at the REAL domain type `T` — so nested locks
  -- inside `E` resolve `x`'s deep peaks through `T`, exactly as the source
  -- rules (subtyping's body premise, abs) type the body at `x:T`.  The codomain
  -- `E` (at sig `(s1,x)`, no self-cvar slot) is lifted by `implicit_cvar`.
  let ctxLock : CompilerCtx (s1,C,x) (s2,C,C,x) :=
    (ctx.weakenTarget.weakenTarget.weakenTarget.consCVar (.unbound .epsilon)
      (.there (.there .here))).consVar T (some .here) (.cvar (.M .epsilon) (.there .here))
  -- the captured resources: the function capture `cs` (weakened past `c`, `x`)
  -- together with the value parameter `{x}`.
  let W : CapyCaptureSet (s1,C,x) :=
    (cs.rename Rename.succ).rename Rename.succ ∪ .var (.M .epsilon) (.bound .here)
  let Ψ : ModalCtx (s2,C,C,x) :=
    ⟨peakSepCtx ctxLock.capyCtx (CapyCaptureSet.peakset ctxLock.capyCtx W) ctxLock.srcCtx, .empty⟩
  .cpoly .unbound {}
    (.typ (.cpoly (.bound (CapyCaptureSet.compile T.captureSet ctxB.srcCtx)) {}
      (.typ (.arrow
              (CapyTy.compile
                ((T.rename Rename.succ).refineCaptureSet (.var (.M .epsilon) (.bound .here)))
                ctxDomain)
              {}
              (.typ (.modal
                      (CapyCaptureSet.compile W ctxLock.srcCtx)
                      Ψ
                      (CapyTy.compile (E.rename Rename.implicit_cvar) ctxLock)))))))
| .poly S cs E, ctx =>
  -- `[X <: S] ->cs E`  ↦  `[X] -> [Ψ]cs E`: a Core `poly` whose body `E` is guarded
  -- by a separation lock `[Ψ]` (a `modal`) capturing `Cf = ⟦cs⟧`.
  let ctxE : CompilerCtx (s1,X) (s2,X) := ctx.weakenTarget.consTVar .top .here
  let Cf : CaptureSet (s2,X) := CapyCaptureSet.compile cs ctx.srcCtx.weaken
  let Ψ  : ModalCtx (s2,X)   :=
    ⟨peakSepCtx ctx.capyCtx (CapyCaptureSet.peakset ctx.capyCtx cs) ctx.srcCtx.weaken, .empty⟩
  .poly
    (CapyTy.compile S ctx)
    {}
    (.typ (.modal Cf Ψ (CapyTy.compile E ctxE)))
| .cpoly cb cs E, ctx =>
  -- `[c <: cb] ->cs E`  ↦  `[c <: ⟦cb⟧] -> [Ψ]cs E`: a Core `cpoly`, exactly like
  -- `poly` but binding a capture variable `c` instead of a type variable.  The
  -- body `E` is guarded by a separation lock `[Ψ]` capturing `Cf = ⟦cs⟧`; besides
  -- the separation of `cs`'s peaks, `Ψ.mutability` re-records the mutability that
  -- `cb` fixes on the introduced parameter `c`.
  let ctxE : CompilerCtx (s1,C) (s2,C) := ctx.weakenTarget.consCVar cb .here
  let Cf : CaptureSet (s2,C) := CapyCaptureSet.compile cs ctx.srcCtx.weaken
  let Ψ  : ModalCtx (s2,C)   :=
    ⟨ peakSepCtx ctx.capyCtx (CapyCaptureSet.peakset ctx.capyCtx cs) ctx.srcCtx.weaken,
      CapyCaptureBound.mutabilityCtx cb .here ⟩
  .cpoly
    (CapyCaptureBound.compile cb ctx.srcCtx)
    {}
    (.typ (.modal Cf Ψ (CapyTy.compile E ctxE)))
| .exi T, ctx =>
  .exi (CapyTy.compile T (ctx.weakenTarget.consCVar (.unbound .epsilon) .here))
termination_by t _ => tySize t
decreasing_by all_goals (simp only [tySize, tySize_rename, tySize_refineCaptureSet]; omega)

end Compilation
