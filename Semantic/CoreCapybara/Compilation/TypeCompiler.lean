import Semantic.CoreCapybara.Compilation.CompilerCtx
open CoreCapybara
namespace Compilation

/-- Compiles a source capture set into the target -/
def CaptureSet.compile : CaptureSet s1 -> SrcCtx s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, ctx => .union (CaptureSet.compile cs1 ctx) (CaptureSet.compile cs2 ctx)
| .cvar a c, ctx => .cvar a (ctx.lookupCVar c)
| .var a (.bound x), ctx => (ctx.lookupVar x).applyAccess a
| .var a (.free n), _ => .var a (.free n)

/-- Compiles a source capture bound into the target.  The mutability annotation
    on an `unbound` source bound has no target counterpart and is dropped. -/
def CapyCaptureBound.compile : CapyCaptureBound s1 -> SrcCtx s1 s2 -> CaptureBound s2
| .unbound _, _ => .unbound
| .bound cs, ctx => .bound (CaptureSet.compile cs ctx)

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

/-- De-duplicates a list (keeping the first occurrence of each element). -/
def dedup [DecidableEq α] : List α -> List α
| [] => []
| a :: as => let d := dedup as; if a ∈ d then d else a :: d

/-- The de-duplicated capture variables of a peak set, with access modes
    discarded. -/
def peakCvars (P : PeakSet s) : List (BVar s .cvar) :=
  dedup (go P.cs)
where
  go : CaptureSet s -> List (BVar s .cvar)
  | .empty => []
  | .union c1 c2 => go c1 ++ go c2
  | .cvar _ c => [c]
  | .var _ _ => []

/-- The access modes at which a given capture variable is accessed in a peak
    set. -/
def accessedAt (P : PeakSet s) (c : BVar s .cvar) : List Access :=
  go P.cs
where
  go : CaptureSet s -> List Access
  | .empty => []
  | .union c1 c2 => go c1 ++ go c2
  | .cvar a c' => if c' = c then [a] else []
  | .var _ _ => []

/-- The capture set holding all access-mode occurrences of a single peak `c` in a
    peak set, e.g. `{.ro c, .drop c}`. -/
def peakItem (P : PeakSet s) (c : BVar s .cvar) : CaptureSet s :=
  (accessedAt P c).foldr (fun a acc => (.cvar a c) ∪ acc) .empty

/-- The separation context of a peak set: one item per distinct peak (capture
    variable), each holding that peak's access-mode occurrences, compiled into the
    target.  Distinct peaks become distinct items and are therefore required to be
    pairwise separate; the several occurrences of one peak share a single item. -/
def peakSepCtx (P : PeakSet s1) (ctx : SrcCtx s1 s2) : SepCtx s2 :=
  (peakCvars P).foldl
    (fun K c => .cons K (CaptureSet.compile (peakItem P c) ctx))
    (.empty : SepCtx s2)

/-- Compiles a source type into the target signature.  The `CompilerCtx` carries
    both the source typing context (`capyCtx`, used to resolve *surface* peaks)
    and the source→target map (`srcCtx`, used to compile capture sets and look up
    variable images). -/
def CapyTy.compile : CapyTy sort s1 -> CompilerCtx s1 s2 -> Ty (CapyTySort.compile sort) s2
-- trivial / structural cases
| .top, _ => .top
| .unit, _ => .unit
| .bool, _ => .bool
| .cap cs, ctx => .cap (CaptureSet.compile cs ctx.srcCtx)
| .cell cs .epsilon, ctx => .cell (CaptureSet.compile cs ctx.srcCtx)
| .cell cs .ro, ctx => .reader (CaptureSet.compile cs ctx.srcCtx)
| .typ T, ctx => .typ (CapyTy.compile T ctx)
| .tvar X, ctx => .tvar (ctx.srcCtx.lookupTVar X)
| .arrow T cs E, ctx =>
  let ctxB : CompilerCtx (s1,C) (s2,C)     :=
    ctx.weakenTarget.consCVar (.unbound .epsilon) .here
  let ctxD : CompilerCtx (s1,C) (s2,C,C)   :=
    ctx.weakenTarget.weakenTarget.consCVar (.unbound .epsilon) (.there .here)
  let ctxE : CompilerCtx (s1,x) (s2,C,C,x) :=
    ctx.weakenTarget.weakenTarget.weakenTarget.consVar
      .top .here (.cvar (.M .epsilon) (.there .here))
  .cpoly .unbound (CaptureSet.compile cs ctx.srcCtx)
    (.typ (.cpoly (.bound (CaptureSet.compile T.captureSet ctxB.srcCtx)) sorry
      (.typ (.arrow
              ((CapyTy.compile T ctxD).refineCaptureSet (.cvar (.M .epsilon) .here))
              sorry
              (.typ (.modal sorry sorry (CapyTy.compile E ctxE)))))))
| .poly S cs E, ctx =>
  -- `[X <: S] ->cs E`  ↦  `[X] -> [Ψ]cs E`: a Core `poly` whose body `E` is guarded
  -- by a separation lock `[Ψ]` (a `modal`) capturing `Cf = ⟦cs⟧`.
  let ctxE : CompilerCtx (s1,X) (s2,X) := ctx.weakenTarget.consTVar .top .here
  let Cf : CaptureSet (s2,X) := CaptureSet.compile cs ctx.srcCtx.weaken
  let Ψ  : ModalCtx (s2,X)   :=
    ⟨peakSepCtx (CapyCaptureSet.peakset ctx.capyCtx cs) ctx.srcCtx.weaken, .empty⟩
  .poly
    (CapyTy.compile S ctx)
    {}
    (.typ (.modal Cf Ψ (CapyTy.compile E ctxE)))
| .cpoly cb cs E, ctx =>
  -- `[c <: cb] ->cs E`  ↦  `[c <: ⟦cb⟧] -> [Ψ]cs E`: a Core `cpoly`, exactly like
  -- `poly` but binding a capture variable `c` instead of a type variable.  The
  -- body `E` is guarded by the same separation lock `[Ψ]` capturing `Cf = ⟦cs⟧`.
  let ctxE : CompilerCtx (s1,C) (s2,C) := ctx.weakenTarget.consCVar cb .here
  let Cf : CaptureSet (s2,C) := CaptureSet.compile cs ctx.srcCtx.weaken
  let Ψ  : ModalCtx (s2,C)   :=
    ⟨peakSepCtx (CapyCaptureSet.peakset ctx.capyCtx cs) ctx.srcCtx.weaken, .empty⟩
  .cpoly
    (CapyCaptureBound.compile cb ctx.srcCtx)
    {}
    (.typ (.modal Cf Ψ (CapyTy.compile E ctxE)))
| .exi T, ctx =>
  .exi (CapyTy.compile T (ctx.weakenTarget.consCVar (.unbound .epsilon) .here))

end Compilation
