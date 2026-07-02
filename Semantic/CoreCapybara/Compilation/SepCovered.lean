import Semantic.CoreCapybara.Compilation.SubtypCompile
import Semantic.CoreCapybara.Compilation.OpenCVarSubtyp
import Semantic.CoreCapybara.Compilation.TargetRename
open CoreCapybara

namespace Compilation

/-!
# The ambient covering-lock invariant (`SepCovered`)

The source rule `CapySepCheck.sep_distinct` postulates that two *distinct* peaks
never alias — separation of distinct capture roots is an axiom of the source
discipline.  The target has no such axiom: every separation fact must be read
off a lock in the context (`SepCheck.sep_lock`).  The bridge is the observation
that **the compiled program always runs under a covering lock**: every compiled
function wraps its body in a `modal` whose lock is `peakSepCtx` over the body
capture's stable peaks (see `CapyTy.compile`'s `arrow`/`poly`/`cpoly` cases), so
inside a function body the ambient context can separate any two distinct stable
peaks of the body's use-set.

`CompilerCtx.SepCovered ctx U` is the *semantic* form of this invariant: any two
distinct stable peaks of `U` have their compiled key items `SepCheck`-separate
in the target context.  It is

* **established** at each binder by the freshly pushed wrap lock
  (`SepCovered.of_lock` — the lock's separation context is literally
  `peakSepCtx` over the same peak set, so `sep_lock` reads the pairs off it);
* **restricted** to any use-set whose stable peaks embed with
  `CapySubcapt`-related key items (`SepCovered.mono`, with the embedding
  provided by `peak_build_of_subcapt` for premise captures below the conclusion
  capture, mirroring `compile_peakSepCtx_subcapt_sep`'s `build`);
* **weakened** along target-only context growth (`SepCovered.weakenTarget`),
  since the source side — peaks, stability, key items — is untouched;
* **consumed** at `unwrap`'s `Satisfy` obligations (the instantiated lock's
  c-free item pairs) and at `CapySepCheck.compile`'s `sep_distinct` leaves.
-/

/-- **The ambient covering-lock invariant** (semantic form).  Any two distinct
    stable peaks of the use-set `U` have their compiled key items separate in
    the target context.  The membership/item vocabulary matches `peakSepCtx`'s
    filtered fold exactly, so `PC.peakSepCtx_hasTwoDistinct_of` connects a
    literal in-context lock to this form. -/
def CompilerCtx.SepCovered {s1 s2 : Sig} (ctx : CompilerCtx s1 s2)
    (U : CapyCaptureSet s1) : Prop :=
  ∀ p1 p2 : Peak s1,
    p1 ∈ (peakList (CapyCaptureSet.peakset ctx.capyCtx U)).filter
        (fun p => decide (Peak.IsStable ctx.capyCtx p)) →
    p2 ∈ (peakList (CapyCaptureSet.peakset ctx.capyCtx U)).filter
        (fun p => decide (Peak.IsStable ctx.capyCtx p)) →
    p1 ≠ p2 →
    SepCheck ctx.coreCtx
      (CapyCaptureSet.compile
        (peakKeyItem (CapyCaptureSet.peakset ctx.capyCtx U) p1) ctx.srcCtx)
      (CapyCaptureSet.compile
        (peakKeyItem (CapyCaptureSet.peakset ctx.capyCtx U) p2) ctx.srcCtx)

/-- The empty use-set is vacuously covered (no peaks, no pairs) — the
    covering hypothesis for a closed whole program's top-level compilation. -/
theorem CompilerCtx.SepCovered.empty {s1 s2 : Sig} {ctx : CompilerCtx s1 s2} :
    ctx.SepCovered (.empty : CapyCaptureSet s1) := by
  intro p1 p2 h1 _ _
  have hmem := (List.mem_filter.mp h1).1
  simp only [CapyCaptureSet.peakset, CapyCaptureSet.peaks, peakList, peakCvars,
    peakPseudos, peakCvars.go, peakPseudos.go, dedup, List.map_nil,
    List.append_nil] at hmem
  exact absurd hmem (List.not_mem_nil)

/-- **Establishment**: a context whose target holds a lock that is (the renaming
    of) `peakSepCtx` over `U`'s peaks is `SepCovered` at `U` — `sep_lock` reads
    every distinct-stable-peak pair off the lock. -/
theorem CompilerCtx.SepCovered.of_lock {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {U : CapyCaptureSet s1} {ℓ : BVar s2 .lock} {μ : MutabilityCtx s2}
    (hlk : Ctx.LookupLock ctx.coreCtx ℓ
      ⟨peakSepCtx ctx.capyCtx (CapyCaptureSet.peakset ctx.capyCtx U) ctx.srcCtx, μ⟩) :
    ctx.SepCovered U := by
  intro p1 p2 h1 h2 hne
  exact SepCheck.sep_lock hlk (PC.peakSepCtx_hasTwoDistinct_of h1 h2 hne)

/-- **Stable-peak transport along `CapySubcapt`** (the reusable core of
    `compile_peakSepCtx_subcapt_sep`'s `build`): every stable peak of a
    subcapture survives as a peak of the supercapture, with its key item
    `CapySubcapt`-below the survivor's. -/
theorem peak_build_of_subcapt {s1 : Sig} {Γ : CapyCtx s1}
    {cs1 cs2 : CapyCaptureSet s1} (h : CapySubcapt Γ cs1 cs2) :
    ∀ p : Peak s1, Peak.IsStable Γ p →
      p ∈ peakList (CapyCaptureSet.peakset Γ cs1) →
      p ∈ peakList (CapyCaptureSet.peakset Γ cs2) ∧
      CapySubcapt Γ (peakKeyItem (CapyCaptureSet.peakset Γ cs1) p)
        (peakKeyItem (CapyCaptureSet.peakset Γ cs2) p) := by
  intro p hpstab hpmem
  cases p with
  | cvar d =>
    simp only [peakKeyItem]
    have hd := PC.mem_peakCvars_of_cvar_mem hpmem
    obtain ⟨a0, hocc⟩ := PC.peakCvars_occ hd
    obtain ⟨a', hmem'⟩ := CapyCtx.peaks_subcapt_stable_subset h hpstab hocc
    exact ⟨PC.cvar_mem_peakList (PC.cvar_mem_peakCvars hmem'),
      peakItem_subcapt_stable h hpstab⟩
  | pseudo D =>
    simp only [peakKeyItem]
    have hD := PC.mem_peakPseudos_of_pseudo_mem hpmem
    obtain ⟨C, hCsub, hCD⟩ := PC.peakPseudos_occ hD
    obtain ⟨C', _, hmem', he⟩ := CapyCtx.peaks_subcapt_pseudo_witness h hCsub
    have hD' : D ∈ peakPseudos (CapyCaptureSet.peakset Γ cs2) :=
      (he.symm.trans hCD) ▸ PC.pseudoBase_mem_peakPseudos hmem'
    exact ⟨PC.pseudo_mem_peakList hD', pseudoItem_subcapt_stable h⟩

/-- **Restriction**: a covering of `U` restricts to any `U'` whose stable peaks
    embed into `U`'s with `CapySubcapt`-related key items (compile the key-item
    subcaptures and shrink both sides with `sep_mono`).  The embedding `hb` is
    `peak_build_of_subcapt h` whenever `CapySubcapt ctx.capyCtx U' U`. -/
theorem CompilerCtx.SepCovered.mono {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {U U' : CapyCaptureSet s1}
    (hcov : ctx.SepCovered U) (hcoh : ctx.SubCoherent)
    (hb : ∀ p : Peak s1, Peak.IsStable ctx.capyCtx p →
      p ∈ peakList (CapyCaptureSet.peakset ctx.capyCtx U') →
      p ∈ peakList (CapyCaptureSet.peakset ctx.capyCtx U) ∧
      CapySubcapt ctx.capyCtx
        (peakKeyItem (CapyCaptureSet.peakset ctx.capyCtx U') p)
        (peakKeyItem (CapyCaptureSet.peakset ctx.capyCtx U) p)) :
    ctx.SepCovered U' := by
  intro p1 p2 h1 h2 hne
  obtain ⟨h1m, h1s⟩ := List.mem_filter.mp h1
  obtain ⟨h2m, h2s⟩ := List.mem_filter.mp h2
  obtain ⟨h1m', hsc1⟩ := hb p1 (decide_eq_true_iff.mp h1s) h1m
  obtain ⟨h2m', hsc2⟩ := hb p2 (decide_eq_true_iff.mp h2s) h2m
  have hbase := hcov p1 p2 (List.mem_filter.mpr ⟨h1m', h1s⟩)
    (List.mem_filter.mpr ⟨h2m', h2s⟩) hne
  exact SepCheck.sep_symm (SepCheck.sep_mono (SepCheck.sep_symm (SepCheck.sep_mono hbase
    (CapySubcapt.compile hsc1 ctx rfl hcoh))) (CapySubcapt.compile hsc2 ctx rfl hcoh))

/-- Restriction along `CapySubcapt` directly (the common instantiation). -/
theorem CompilerCtx.SepCovered.of_subcapt {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {U U' : CapyCaptureSet s1}
    (hcov : ctx.SepCovered U) (hcoh : ctx.SubCoherent)
    (h : CapySubcapt ctx.capyCtx U' U) :
    ctx.SepCovered U' :=
  hcov.mono hcoh (peak_build_of_subcapt h)

/-- **Target-only weakening**: pushing a (closed) target binding preserves the
    covering — the source side (peaks, stability, key items) is untouched, and
    the established separations transport by the injective push renaming. -/
theorem CompilerCtx.SepCovered.weakenTarget {s1 s2 : Sig} {ctx : CompilerCtx s1 s2}
    {U : CapyCaptureSet s1} {k : Kind} {b : Binding s2 k}
    (hcov : ctx.SepCovered U) :
    (ctx.weakenTarget b).SepCovered U := by
  intro p1 p2 h1 h2 hne
  have hbase := hcov p1 p2 h1 h2 hne
  have hw := hbase.renamesTo (Ctx.RenamesTo.weaken b) Rename.injective_succ
  simp only [CompilerCtx.weakenTarget, SrcCtx.weaken, CapyCaptureSet.compile_rename]
  exact hw

end Compilation
