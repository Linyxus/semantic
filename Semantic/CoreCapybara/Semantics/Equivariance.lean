import Semantic.CoreCapybara.Semantics.BigStep

/-! # Location renaming and equivariance (nominal layer)

  Heap locations are the free variables `.free l : Var k {}`.  `renameLoc π`
  transports a permutation `π : Equiv.Perm Nat` through every location-bearing
  object, leaving De Bruijn structure (`.bound`, signatures) untouched — so it is
  signature-preserving and orthogonal to `Exp.rename`/`Exp.subst`.

  This module is the infrastructure for Church–Rosser up to `Trace.Equiv` and
  `Memory.Iso`: confluence is only provable up to a location bijection because
  `step_alloc` chooses fresh names freely (two runs diverge at a single `alloc`).

  STATUS: definitions, `Iso`/`ConfigIso`, functoriality, and predicate transport
  are proven; the equivariance OBLIGATIONS (data-level `*_renameLoc` and the
  operational `Step/BigStep/Reduce.renameLoc`) are stated and grouped for design
  audit, proofs to follow in the next phase. -/

namespace CoreCapybara

/-! ## Renaming on syntax

  Each `renameLoc` mirrors the corresponding `subst`/`rename`, but acts only on
  the `.free` locations (the heap addresses), recursing structurally everywhere
  else. -/

/-- Rename the heap location of a (free) variable; bound variables are fixed. -/
def Var.renameLoc (π : Equiv.Perm Nat) : Var k s → Var k s
| .bound x => .bound x
| .free n => .free (π n)

/-- Rename all free locations in a capture set. -/
def CaptureSet.renameLoc (π : Equiv.Perm Nat) : CaptureSet s → CaptureSet s
| .empty => .empty
| .union a b => .union (a.renameLoc π) (b.renameLoc π)
| .var m x => .var m (x.renameLoc π)
| .cvar m x => .cvar m x

/-- Rename all free locations in a capture bound. -/
def CaptureBound.renameLoc (π : Equiv.Perm Nat) : CaptureBound s → CaptureBound s
| .unbound => .unbound
| .bound cs => .bound (cs.renameLoc π)

/-- Rename all free locations in a separation context. -/
def SepCtx.renameLoc (π : Equiv.Perm Nat) : SepCtx s → SepCtx s
| .empty => .empty
| .cons K C m => .cons (K.renameLoc π) (C.renameLoc π) m

/-- Rename all free locations in a type. -/
def Ty.renameLoc (π : Equiv.Perm Nat) : Ty sort s → Ty sort s
| .top => .top
| .tvar x => .tvar x
| .arrow T1 cs T2 => .arrow (T1.renameLoc π) (cs.renameLoc π) (T2.renameLoc π)
| .poly T1 cs T2 => .poly (T1.renameLoc π) (cs.renameLoc π) (T2.renameLoc π)
| .cpoly cb cs T => .cpoly (cb.renameLoc π) (cs.renameLoc π) (T.renameLoc π)
| .modal cs Ψ T => .modal (cs.renameLoc π) (Ψ.renameLoc π) (T.renameLoc π)
| .unit => .unit
| .cap cs => .cap (cs.renameLoc π)
| .bool => .bool
| .cell cs => .cell (cs.renameLoc π)
| .reader cs => .reader (cs.renameLoc π)
| .exi T => .exi (T.renameLoc π)
| .typ T => .typ (T.renameLoc π)

/-- `renameLoc` preserves emptiness of a capture set. -/
theorem CaptureSet.IsEmpty.renameLoc {cs : CaptureSet s} (h : cs.IsEmpty)
    (π : Equiv.Perm Nat) : (cs.renameLoc π).IsEmpty := by
  induction h with
  | empty => exact .empty
  | union _ _ ih1 ih2 => exact .union ih1 ih2

/-- `renameLoc` commutes with the top-level capture-set extractor on types. -/
theorem Ty.captureSet_renameLoc {T : Ty .capt s} (π : Equiv.Perm Nat) :
    (T.renameLoc π).captureSet = T.captureSet.renameLoc π := by
  cases T <;> rfl

/-- `renameLoc` preserves purity of a type. -/
theorem Ty.IsPureType.renameLoc {T : Ty .capt s} (h : T.IsPureType)
    (π : Equiv.Perm Nat) : (T.renameLoc π).IsPureType := by
  unfold Ty.IsPureType at h ⊢
  rw [Ty.captureSet_renameLoc]
  exact h.renameLoc π

/-- Rename all free locations in a pure type (transporting the purity proof). -/
def PureTy.renameLoc (π : Equiv.Perm Nat) (T : PureTy s) : PureTy s :=
  ⟨T.core.renameLoc π, T.p.renameLoc π⟩

/-- Rename all free locations in an expression. -/
def Exp.renameLoc (π : Equiv.Perm Nat) : Exp s → Exp s
| .var x => .var (x.renameLoc π)
| .abs cs T e => .abs (cs.renameLoc π) (T.renameLoc π) (e.renameLoc π)
| .tabs cs T e => .tabs (cs.renameLoc π) (T.renameLoc π) (e.renameLoc π)
| .cabs cs cb e => .cabs (cs.renameLoc π) (cb.renameLoc π) (e.renameLoc π)
| .boxed cs Ψ e => .boxed (cs.renameLoc π) (Ψ.renameLoc π) (e.renameLoc π)
| .reader x => .reader (x.renameLoc π)
| .alloc x => .alloc (x.renameLoc π)
| .drop x => .drop (x.renameLoc π)
| .pack cs x => .pack (cs.renameLoc π) (x.renameLoc π)
| .app x y => .app (x.renameLoc π) (y.renameLoc π)
| .tapp x T => .tapp (x.renameLoc π) (T.renameLoc π)
| .capp x cs => .capp (x.renameLoc π) (cs.renameLoc π)
| .unwrap x => .unwrap (x.renameLoc π)
| .letin e1 e2 => .letin (e1.renameLoc π) (e2.renameLoc π)
| .unpack e1 e2 => .unpack (e1.renameLoc π) (e2.renameLoc π)
| .unit => .unit
| .btrue => .btrue
| .bfalse => .bfalse
| .read x => .read (x.renameLoc π)
| .write x y => .write (x.renameLoc π) (y.renameLoc π)
| .cond x e2 e3 => .cond (x.renameLoc π) (e2.renameLoc π) (e3.renameLoc π)
| .par C1 C2 e1 e2 => .par (C1.renameLoc π) (C2.renameLoc π) (e1.renameLoc π) (e2.renameLoc π)

/-! ### Predicate transport (value/answer shapes are preserved by `renameLoc`) -/

theorem Exp.IsSimpleVal.renameLoc {e : Exp s} (h : e.IsSimpleVal) (π : Equiv.Perm Nat) :
    (e.renameLoc π).IsSimpleVal := by
  cases h <;> exact (by constructor)

theorem Exp.IsVal.renameLoc {e : Exp s} (h : e.IsVal) (π : Equiv.Perm Nat) :
    (e.renameLoc π).IsVal := by
  cases h <;> exact (by constructor)

theorem Exp.IsAns.renameLoc {e : Exp {}} (h : e.IsAns) (π : Equiv.Perm Nat) :
    (e.renameLoc π).IsAns := by
  cases h with
  | is_val hv => exact .is_val (hv.renameLoc π)
  | is_var => exact .is_var

/-! ## Renaming on the runtime store -/

/-- Rename all locations in a runtime capability set. -/
def CapabilitySet.renameLoc (π : Equiv.Perm Nat) : CapabilitySet → CapabilitySet
| .empty => .empty
| .cap m l => .cap m (π l)
| .union a b => .union (a.renameLoc π) (b.renameLoc π)

/-- Rename the value bundled in a heap value (transporting the value proof). -/
def HeapVal.renameLoc (π : Equiv.Perm Nat) (hv : HeapVal) : HeapVal where
  unwrap := hv.unwrap.renameLoc π
  isVal := hv.isVal.renameLoc π
  reachability := hv.reachability.renameLoc π

/-- Rename a heap cell.  Capability cells carry no location (the location is the
    heap key), so only the stored value is rewritten. -/
def Cell.renameLoc (π : Equiv.Perm Nat) : Cell → Cell
| .val hv => .val (hv.renameLoc π)
| .capability info => .capability info
| .masked => .masked

/-- Rename a heap: the cell at `l` moves to `π l`, with its contents rewritten.
    Defined by preimage, so `(h.renameLoc π) (π l) = (h l).map (·.renameLoc π)`. -/
def Heap.renameLoc (π : Equiv.Perm Nat) (h : Heap) : Heap :=
  fun l => (h (π.symm l)).map (Cell.renameLoc π)

/-- Rename a trace item. -/
def TraceItem.renameLoc (π : Equiv.Perm Nat) : TraceItem → TraceItem
| .access mu l => .access mu (π l)
| .alloc l => .alloc (π l)
| .dealloc l => .dealloc (π l)

/-- Rename a trace. -/
def Trace.renameLoc (π : Equiv.Perm Nat) (t : Trace) : Trace :=
  t.map (TraceItem.renameLoc π)

/-! ## Equivariance obligations (data level)

  These are the facts the bundled-structure renamings and the operational
  equivariance rest on.  Proofs deferred to the post-audit phase. -/

/-- Heap lookup commutes with renaming (along `π`). -/
theorem Heap.lookup_renameLoc (π : Equiv.Perm Nat) (h : Heap) (l : Nat) :
    (h.renameLoc π) (π l) = (h l).map (Cell.renameLoc π) := by
  unfold Heap.renameLoc
  rw [Equiv.symm_apply_apply]

/-- `reachability_of_loc` is equivariant. -/
theorem reachability_of_loc_renameLoc (π : Equiv.Perm Nat) (h : Heap) (l : Nat) :
    reachability_of_loc (h.renameLoc π) (π l)
      = (reachability_of_loc h l).renameLoc π := by
  sorry

/-- `expand_captures` is equivariant. -/
theorem expand_captures_renameLoc (π : Equiv.Perm Nat) (h : Heap) (cs : CaptureSet {}) :
    expand_captures (h.renameLoc π) (cs.renameLoc π)
      = (expand_captures h cs).renameLoc π := by
  sorry

/-- `compute_reachability` is equivariant. -/
theorem compute_reachability_renameLoc (π : Equiv.Perm Nat) (h : Heap)
    (v : Exp {}) (hv : v.IsSimpleVal) :
    compute_reachability (h.renameLoc π) (v.renameLoc π) (hv.renameLoc π)
      = (compute_reachability h v hv).renameLoc π := by
  sorry

/-- Membership in a renamed capability set tracks the renamed location. -/
theorem CapabilitySet.hasmem_renameLoc (π : Equiv.Perm Nat) {C : CapabilitySet}
    {m : CapMode} {l : Nat} :
    (C.renameLoc π).hasmem m (π l) ↔ C.hasmem m l := by
  sorry

/-- Push a location renaming through a substitution: rename the locations in its
    image. (`σ` maps De Bruijn variables to terms; `renameLoc` rewrites the free
    locations of those terms.) -/
def Subst.renameLoc (π : Equiv.Perm Nat) (σ : Subst s1 s2) : Subst s1 s2 where
  var := fun x => (σ.var x).renameLoc π
  tvar := fun x => (σ.tvar x).renameLoc π
  cvar := fun x => (σ.cvar x).renameLoc π

/-- `renameLoc` commutes with `subst` (the linchpin): renaming free locations is
    orthogonal to De Bruijn substitution. -/
theorem Exp.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (e : Exp s1) (σ : Subst s1 s2) :
    (e.subst σ).renameLoc π = (e.renameLoc π).subst (σ.renameLoc π) := by
  sorry

/-- Specialised linchpin for opening a value binder with a location. -/
theorem Exp.openVar_renameLoc (π : Equiv.Perm Nat) {s : Sig}
    (e : Exp (s,x)) (y : Nat) :
    (e.subst (Subst.openVar (.free y))).renameLoc π
      = (e.renameLoc π).subst (Subst.openVar (.free (π y))) := by
  sorry

/-- Expression well-formedness is equivariant. -/
theorem Exp.WfInHeap.renameLoc {e : Exp s} {h : Heap} (hwf : e.WfInHeap h)
    (π : Equiv.Perm Nat) : (e.renameLoc π).WfInHeap (h.renameLoc π) := by
  sorry

/-- Heap well-formedness is equivariant. -/
theorem Heap.WfHeap.renameLoc {h : Heap} (hwf : h.WfHeap) (π : Equiv.Perm Nat) :
    (h.renameLoc π).WfHeap := by
  sorry

/-- A renamed heap has finite domain (the image of the original domain). -/
theorem Heap.HasFinDom.renameLoc {h : Heap} {dom : Finset Nat}
    (hdom : h.HasFinDom dom) (π : Equiv.Perm Nat) :
    (h.renameLoc π).HasFinDom (dom.image π) := by
  sorry

/-- Rename a memory (transporting the well-formedness and finiteness proofs). -/
def Memory.renameLoc (π : Equiv.Perm Nat) (m : Memory) : Memory where
  heap := m.heap.renameLoc π
  wf := m.wf.renameLoc π
  findom :=
    let ⟨dom, hdom⟩ := m.findom
    ⟨dom.image π, hdom.renameLoc π⟩

/-- Memory lookup commutes with renaming (along `π`). -/
theorem Memory.lookup_renameLoc (π : Equiv.Perm Nat) (m : Memory) (l : Nat) :
    (m.renameLoc π).lookup (π l) = (m.lookup l).map (Cell.renameLoc π) :=
  Heap.lookup_renameLoc π m.heap l

/-! ## Functoriality -/

theorem Var.renameLoc_id {x : Var k s} : x.renameLoc (Equiv.refl Nat) = x := by
  cases x <;> rfl

theorem CaptureSet.renameLoc_id {cs : CaptureSet s} :
    cs.renameLoc (Equiv.refl Nat) = cs := by
  induction cs with
  | empty => rfl
  | union _ _ ih1 ih2 => simp only [CaptureSet.renameLoc, ih1, ih2]
  | var m x => simp only [CaptureSet.renameLoc, Var.renameLoc_id]
  | cvar m x => rfl

theorem Trace.renameLoc_id {t : Trace} : t.renameLoc (Equiv.refl Nat) = t := by
  unfold Trace.renameLoc
  induction t with
  | nil => rfl
  | cons it t ih =>
    simp only [List.map_cons, ih]
    cases it <;> rfl

theorem CapabilitySet.renameLoc_id {C : CapabilitySet} :
    C.renameLoc (Equiv.refl Nat) = C := by
  induction C with
  | empty => rfl
  | cap m l => rfl
  | union _ _ ih1 ih2 => simp only [CapabilitySet.renameLoc, ih1, ih2]

/-- `Exp.renameLoc` by the identity permutation is the identity. -/
theorem Exp.renameLoc_id {e : Exp s} : e.renameLoc (Equiv.refl Nat) = e := by
  sorry

/-! ## Memory and configuration isomorphism

  Two memories are isomorphic when one is a location-renaming of the other; two
  configurations are isomorphic under a SINGLE permutation simultaneously
  renaming the memory and the running expression. -/

/-- `m1.Iso m2`: `m2` is `m1` up to a location renaming. -/
def Memory.Iso (m1 m2 : Memory) : Prop := ∃ π : Equiv.Perm Nat, m2 = m1.renameLoc π

/-- Configuration isomorphism: memory and expression renamed by one `π`. -/
def ConfigIso (m1 : Memory) (e1 : Exp {}) (m2 : Memory) (e2 : Exp {}) : Prop :=
  ∃ π : Equiv.Perm Nat, m2 = m1.renameLoc π ∧ e2 = e1.renameLoc π

theorem Memory.Iso.refl (m : Memory) : m.Iso m :=
  ⟨Equiv.refl Nat, by sorry⟩

theorem Memory.Iso.symm {m1 m2 : Memory} (h : m1.Iso m2) : m2.Iso m1 := by
  sorry

theorem Memory.Iso.trans {m1 m2 m3 : Memory} (h1 : m1.Iso m2) (h2 : m2.Iso m3) :
    m1.Iso m3 := by
  sorry

/-! ## Operational equivariance (the payoff)

  Every operational relation is closed under simultaneous location renaming.
  These are the theorems the Church–Rosser proof consumes (to resolve the
  fresh-name clash by renaming one side of a divergence). Proofs deferred. -/

/-- A single step is equivariant. -/
theorem Step.renameLoc {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hstep : Step t m e m' e') (π : Equiv.Perm Nat) :
    Step (t.renameLoc π) (m.renameLoc π) (e.renameLoc π) (m'.renameLoc π) (e'.renameLoc π) := by
  sorry

/-- A multi-step reduction is equivariant. -/
theorem Reduce.renameLoc {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hred : Reduce t m e m' e') (π : Equiv.Perm Nat) :
    Reduce (t.renameLoc π) (m.renameLoc π) (e.renameLoc π) (m'.renameLoc π) (e'.renameLoc π) := by
  sorry

/-- A single sequential step is equivariant. -/
theorem SeqStep.renameLoc {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hstep : SeqStep t m e m' e') (π : Equiv.Perm Nat) :
    SeqStep (t.renameLoc π) (m.renameLoc π) (e.renameLoc π) (m'.renameLoc π) (e'.renameLoc π) := by
  sorry

/-- A multi-step sequential reduction is equivariant. -/
theorem SeqReduce.renameLoc {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hred : SeqReduce t m e m' e') (π : Equiv.Perm Nat) :
    SeqReduce (t.renameLoc π) (m.renameLoc π) (e.renameLoc π) (m'.renameLoc π) (e'.renameLoc π) := by
  sorry

/-- A big-step evaluation is equivariant. -/
theorem BigStep.renameLoc {t : Trace} {m m' : Memory} {e v : Exp {}}
    (hbs : BigStep m e t v m') (π : Equiv.Perm Nat) :
    BigStep (m.renameLoc π) (e.renameLoc π) (t.renameLoc π) (v.renameLoc π) (m'.renameLoc π) := by
  sorry

end CoreCapybara
