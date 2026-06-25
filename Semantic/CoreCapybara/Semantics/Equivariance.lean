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
| .cons K C => .cons (K.renameLoc π) (C.renameLoc π)

/-- Rename all free locations in a mutability context. -/
def MutabilityCtx.renameLoc (π : Equiv.Perm Nat) : MutabilityCtx s → MutabilityCtx s
| .empty => .empty
| .cons K C m => .cons (K.renameLoc π) (C.renameLoc π) m

/-- Rename all free locations in a modal context, componentwise. -/
def ModalCtx.renameLoc (π : Equiv.Perm Nat) (Ψ : ModalCtx s) : ModalCtx s :=
  ⟨Ψ.sep.renameLoc π, Ψ.mutability.renameLoc π⟩

@[simp] theorem ModalCtx.renameLoc_sep {π : Equiv.Perm Nat} {Ψ : ModalCtx s} :
    (Ψ.renameLoc π).sep = Ψ.sep.renameLoc π := rfl

@[simp] theorem ModalCtx.renameLoc_mutability {π : Equiv.Perm Nat} {Ψ : ModalCtx s} :
    (Ψ.renameLoc π).mutability = Ψ.mutability.renameLoc π := rfl

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

/-- Two pure types are equal once their cores agree (the purity proof is a Prop). -/
theorem PureTy.eq_of_core {T1 T2 : PureTy s} (h : T1.core = T2.core) : T1 = T2 := by
  cases T1; cases T2; cases h; rfl

/-! ### `renameLoc` commutes with De Bruijn `rename` (disjoint variable classes) -/

theorem Var.renameLoc_rename (π : Equiv.Perm Nat) (f : Rename s1 s2) (x : Var k s1) :
    (x.rename f).renameLoc π = (x.renameLoc π).rename f := by
  cases x <;> rfl

theorem CaptureSet.renameLoc_rename (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (f : Rename s1 s2) (cs : CaptureSet s1) :
    (cs.rename f).renameLoc π = (cs.renameLoc π).rename f := by
  induction cs generalizing s2 with
  | empty => rfl
  | union a b iha ihb => simp only [CaptureSet.rename, CaptureSet.renameLoc, iha, ihb]
  | var m x => simp only [CaptureSet.rename, CaptureSet.renameLoc, Var.renameLoc_rename]
  | cvar m x => rfl

theorem CaptureBound.renameLoc_rename (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (f : Rename s1 s2) (cb : CaptureBound s1) :
    (cb.rename f).renameLoc π = (cb.renameLoc π).rename f := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CaptureBound.rename, CaptureBound.renameLoc, CaptureSet.renameLoc_rename]

theorem SepCtx.renameLoc_rename (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (f : Rename s1 s2) (K : SepCtx s1) :
    (K.rename f).renameLoc π = (K.renameLoc π).rename f := by
  induction K generalizing s2 with
  | empty => rfl
  | cons K C ih =>
    simp only [SepCtx.rename, SepCtx.renameLoc, ih, CaptureSet.renameLoc_rename]

theorem MutabilityCtx.renameLoc_rename (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (f : Rename s1 s2) (K : MutabilityCtx s1) :
    (K.rename f).renameLoc π = (K.renameLoc π).rename f := by
  induction K generalizing s2 with
  | empty => rfl
  | cons K C m ih =>
    simp only [MutabilityCtx.rename, MutabilityCtx.renameLoc, ih, CaptureSet.renameLoc_rename]

theorem ModalCtx.renameLoc_rename (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (f : Rename s1 s2) (K : ModalCtx s1) :
    (K.rename f).renameLoc π = (K.renameLoc π).rename f := by
  cases K with
  | mk sep mu =>
    simp only [ModalCtx.rename, ModalCtx.renameLoc,
      SepCtx.renameLoc_rename, MutabilityCtx.renameLoc_rename]

theorem Ty.renameLoc_rename (π : Equiv.Perm Nat) {sort : TySort} {s1 s2 : Sig}
    (f : Rename s1 s2) (T : Ty sort s1) :
    (T.rename f).renameLoc π = (T.renameLoc π).rename f := by
  induction T generalizing s2 with
  | top => rfl
  | tvar x => rfl
  | unit => rfl
  | bool => rfl
  | arrow _ _ _ ih1 ih2 =>
    simp only [Ty.rename, Ty.renameLoc, CaptureSet.renameLoc_rename, ih1, ih2]
  | poly _ _ _ ih1 ih2 =>
    simp only [Ty.rename, Ty.renameLoc, CaptureSet.renameLoc_rename, ih1, ih2]
  | cpoly _ _ _ ih =>
    simp only [Ty.rename, Ty.renameLoc, CaptureSet.renameLoc_rename,
      CaptureBound.renameLoc_rename, ih]
  | modal _ _ _ ih =>
    simp only [Ty.rename, Ty.renameLoc, CaptureSet.renameLoc_rename,
      ModalCtx.renameLoc_rename, ih]
  | cap _ => simp only [Ty.rename, Ty.renameLoc, CaptureSet.renameLoc_rename]
  | cell _ => simp only [Ty.rename, Ty.renameLoc, CaptureSet.renameLoc_rename]
  | reader _ => simp only [Ty.rename, Ty.renameLoc, CaptureSet.renameLoc_rename]
  | exi _ ih => simp only [Ty.rename, Ty.renameLoc, ih]
  | typ _ ih => simp only [Ty.rename, Ty.renameLoc, ih]

theorem PureTy.renameLoc_rename (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (f : Rename s1 s2) (T : PureTy s1) :
    (T.rename f).renameLoc π = (T.renameLoc π).rename f := by
  apply PureTy.eq_of_core
  simp only [PureTy.rename, PureTy.renameLoc, Ty.renameLoc_rename]

theorem Exp.renameLoc_rename (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (f : Rename s1 s2) (e : Exp s1) :
    (e.rename f).renameLoc π = (e.renameLoc π).rename f := by
  induction e generalizing s2 with
  | var x => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename]
  | abs _ _ _ ih => simp only [Exp.rename, Exp.renameLoc, CaptureSet.renameLoc_rename,
      Ty.renameLoc_rename, ih]
  | tabs _ _ _ ih => simp only [Exp.rename, Exp.renameLoc, CaptureSet.renameLoc_rename,
      PureTy.renameLoc_rename, ih]
  | cabs _ _ _ ih => simp only [Exp.rename, Exp.renameLoc, CaptureSet.renameLoc_rename,
      CaptureBound.renameLoc_rename, ih]
  | boxed _ _ _ ih => simp only [Exp.rename, Exp.renameLoc, CaptureSet.renameLoc_rename,
      ModalCtx.renameLoc_rename, ih]
  | reader x => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename]
  | alloc x => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename]
  | drop x => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename]
  | pack _ x => simp only [Exp.rename, Exp.renameLoc, CaptureSet.renameLoc_rename,
      Var.renameLoc_rename]
  | app x y => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename]
  | tapp x _ => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename,
      PureTy.renameLoc_rename]
  | capp x _ => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename,
      CaptureSet.renameLoc_rename]
  | unwrap x => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename]
  | letin _ _ ih1 ih2 => simp only [Exp.rename, Exp.renameLoc, ih1, ih2]
  | unpack _ _ ih1 ih2 => simp only [Exp.rename, Exp.renameLoc, ih1, ih2]
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename]
  | write x y => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename]
  | cond x _ _ ih1 ih2 => simp only [Exp.rename, Exp.renameLoc, Var.renameLoc_rename, ih1, ih2]
  | par _ _ _ _ ih1 ih2 => simp only [Exp.rename, Exp.renameLoc, CaptureSet.renameLoc_rename,
      ih1, ih2]

/-! ### `renameLoc` commutes with mode operations (location-preserving) -/

theorem CaptureSet.applyRO_renameLoc (π : Equiv.Perm Nat) (cs : CaptureSet s) :
    (cs.applyRO).renameLoc π = (cs.renameLoc π).applyRO := by
  induction cs with
  | empty => rfl
  | union a b iha ihb => simp only [CaptureSet.applyRO, CaptureSet.renameLoc, iha, ihb]
  | var a x => rfl
  | cvar a x => rfl

theorem CaptureSet.applyMut_renameLoc (π : Equiv.Perm Nat) (m : Mutability)
    (cs : CaptureSet s) : (cs.applyMut m).renameLoc π = (cs.renameLoc π).applyMut m := by
  cases m with
  | epsilon => rfl
  | ro => simp only [CaptureSet.applyMut, CaptureSet.applyRO_renameLoc]

theorem CaptureSet.applyDrop_renameLoc (π : Equiv.Perm Nat) (cs : CaptureSet s) :
    (cs.applyDrop).renameLoc π = (cs.renameLoc π).applyDrop := by
  induction cs with
  | empty => rfl
  | union a b iha ihb => simp only [CaptureSet.applyDrop, CaptureSet.renameLoc, iha, ihb]
  | var a x => rfl
  | cvar a x => rfl

theorem CaptureSet.applyAccess_renameLoc (π : Equiv.Perm Nat) (a : Access)
    (cs : CaptureSet s) : (cs.applyAccess a).renameLoc π = (cs.renameLoc π).applyAccess a := by
  cases a with
  | M m => simp only [CaptureSet.applyAccess, CaptureSet.applyMut_renameLoc]
  | drop => simp only [CaptureSet.applyAccess, CaptureSet.applyDrop_renameLoc]

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

/-- `renameLoc` commutes with the runtime capability-set mode operations. -/
theorem CapabilitySet.applyRO_renameLoc (π : Equiv.Perm Nat) (C : CapabilitySet) :
    (C.applyRO).renameLoc π = (C.renameLoc π).applyRO := by
  induction C with
  | empty => rfl
  | cap m l => rfl
  | union _ _ ih1 ih2 => simp only [CapabilitySet.applyRO, CapabilitySet.renameLoc, ih1, ih2]

theorem CapabilitySet.to_drop_renameLoc (π : Equiv.Perm Nat) (C : CapabilitySet) :
    (C.to_drop).renameLoc π = (C.renameLoc π).to_drop := by
  induction C with
  | empty => rfl
  | cap m l => rfl
  | union _ _ ih1 ih2 => simp only [CapabilitySet.to_drop, CapabilitySet.renameLoc, ih1, ih2]

theorem CapabilitySet.applyMut_renameLoc (π : Equiv.Perm Nat) (m : Mutability)
    (C : CapabilitySet) : (C.applyMut m).renameLoc π = (C.renameLoc π).applyMut m := by
  cases m with
  | epsilon => rfl
  | ro => simp only [CapabilitySet.applyMut, CapabilitySet.applyRO_renameLoc]

theorem CapabilitySet.applyAccess_renameLoc (π : Equiv.Perm Nat) (a : Access)
    (C : CapabilitySet) : (C.applyAccess a).renameLoc π = (C.renameLoc π).applyAccess a := by
  cases a with
  | M m => simp only [CapabilitySet.applyAccess, CapabilitySet.applyMut_renameLoc]
  | drop => simp only [CapabilitySet.applyAccess, CapabilitySet.to_drop_renameLoc]

theorem CapabilitySet.singleton_renameLoc (π : Equiv.Perm Nat) (m : Mutability) (l : Nat) :
    (CapabilitySet.singleton m l).renameLoc π = CapabilitySet.singleton m (π l) := rfl

/-- `reachability_of_loc` is equivariant. -/
theorem reachability_of_loc_renameLoc (π : Equiv.Perm Nat) (h : Heap) (l : Nat) :
    reachability_of_loc (h.renameLoc π) (π l)
      = (reachability_of_loc h l).renameLoc π := by
  unfold reachability_of_loc
  rw [Heap.lookup_renameLoc]
  cases h l with
  | none => rfl
  | some c =>
    cases c with
    | capability ci => exact (CapabilitySet.singleton_renameLoc π .epsilon l).symm
    | val hv => rfl
    | masked => exact (CapabilitySet.singleton_renameLoc π .epsilon l).symm

/-- `expand_captures` is equivariant. -/
theorem expand_captures_renameLoc (π : Equiv.Perm Nat) (h : Heap) (cs : CaptureSet {}) :
    expand_captures (h.renameLoc π) (cs.renameLoc π)
      = (expand_captures h cs).renameLoc π := by
  induction cs with
  | empty => rfl
  | union a b iha ihb =>
    simp only [CaptureSet.renameLoc, expand_captures, iha, ihb]
    rfl
  | var m x =>
    cases x with
    | bound b => cases b
    | free loc =>
      simp only [CaptureSet.renameLoc, Var.renameLoc, expand_captures,
        reachability_of_loc_renameLoc, CapabilitySet.applyAccess_renameLoc]
  | cvar m x => cases x

/-- `compute_reachability` is equivariant. -/
theorem compute_reachability_renameLoc (π : Equiv.Perm Nat) (h : Heap)
    (v : Exp {}) (hv : v.IsSimpleVal) :
    compute_reachability (h.renameLoc π) (v.renameLoc π) (hv.renameLoc π)
      = (compute_reachability h v hv).renameLoc π := by
  cases hv with
  | abs => simp only [Exp.renameLoc, compute_reachability, expand_captures_renameLoc]
  | tabs => simp only [Exp.renameLoc, compute_reachability, expand_captures_renameLoc]
  | cabs => simp only [Exp.renameLoc, compute_reachability, expand_captures_renameLoc]
  | boxed => simp only [Exp.renameLoc, compute_reachability, expand_captures_renameLoc]
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | reader =>
    rename_i x
    cases x with
    | bound b => cases b
    | free loc => rfl

/-- Membership in a renamed capability set tracks the renamed location. -/
theorem CapabilitySet.hasmem_renameLoc (π : Equiv.Perm Nat) {C : CapabilitySet}
    {m : CapMode} {l : Nat} :
    (C.renameLoc π).hasmem m (π l) ↔ C.hasmem m l := by
  induction C with
  | empty =>
    exact ⟨fun h => (CapabilitySet.not_hasmem_empty h).elim,
           fun h => (CapabilitySet.not_hasmem_empty h).elim⟩
  | cap m' l' =>
    simp only [CapabilitySet.renameLoc, CapabilitySet.hasmem_cap_iff]
    constructor
    · rintro ⟨rfl, hl⟩; exact ⟨rfl, π.injective hl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  | union C1 C2 ih1 ih2 =>
    constructor
    · intro hh
      cases hh with
      | left h => exact .left (ih1.mp h)
      | right h => exact .right (ih2.mp h)
    · intro hh
      cases hh with
      | left h => exact .left (ih1.mpr h)
      | right h => exact .right (ih2.mpr h)

/-- Push a location renaming through a substitution: rename the locations in its
    image. (`σ` maps De Bruijn variables to terms; `renameLoc` rewrites the free
    locations of those terms.) -/
def Subst.renameLoc (π : Equiv.Perm Nat) (σ : Subst s1 s2) : Subst s1 s2 where
  var := fun x => (σ.var x).renameLoc π
  tvar := fun x => (σ.tvar x).renameLoc π
  cvar := fun x => (σ.cvar x).renameLoc π

/-- Pushing a renaming through `Subst.lift` commutes with lifting the pushed
    substitution. -/
theorem Subst.lift_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig} (σ : Subst s1 s2)
    {k : Kind} : (σ.lift (k:=k)).renameLoc π = (σ.renameLoc π).lift (k:=k) := by
  apply Subst.funext
  · intro x
    cases x with
    | here => rfl
    | there x => exact Var.renameLoc_rename π Rename.succ (σ.var x)
  · intro X
    cases X with
    | here => rfl
    | there X => exact PureTy.renameLoc_rename π Rename.succ (σ.tvar X)
  · intro C
    cases C with
    | here => rfl
    | there C => exact CaptureSet.renameLoc_rename π Rename.succ (σ.cvar C)

theorem Var.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (x : Var .var s1) (σ : Subst s1 s2) :
    (x.subst σ).renameLoc π = (x.renameLoc π).subst (σ.renameLoc π) := by
  cases x <;> rfl

theorem CaptureSet.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (cs : CaptureSet s1) (σ : Subst s1 s2) :
    (cs.subst σ).renameLoc π = (cs.renameLoc π).subst (σ.renameLoc π) := by
  induction cs with
  | empty => rfl
  | union a b iha ihb => simp only [CaptureSet.subst, CaptureSet.renameLoc, iha, ihb]
  | var m x => simp only [CaptureSet.subst, CaptureSet.renameLoc, Var.subst_renameLoc]
  | cvar m x =>
    simp only [CaptureSet.subst, CaptureSet.renameLoc, CaptureSet.applyAccess_renameLoc,
      Subst.renameLoc]

theorem CaptureBound.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (cb : CaptureBound s1) (σ : Subst s1 s2) :
    (cb.subst σ).renameLoc π = (cb.renameLoc π).subst (σ.renameLoc π) := by
  cases cb with
  | unbound => rfl
  | bound cs =>
    simp only [CaptureBound.subst, CaptureBound.renameLoc, CaptureSet.subst_renameLoc]

theorem SepCtx.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (K : SepCtx s1) (σ : Subst s1 s2) :
    (K.subst σ).renameLoc π = (K.renameLoc π).subst (σ.renameLoc π) := by
  induction K with
  | empty => rfl
  | cons K C ih =>
    simp only [SepCtx.subst, SepCtx.renameLoc, ih, CaptureSet.subst_renameLoc]

theorem MutabilityCtx.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (K : MutabilityCtx s1) (σ : Subst s1 s2) :
    (K.subst σ).renameLoc π = (K.renameLoc π).subst (σ.renameLoc π) := by
  induction K with
  | empty => rfl
  | cons K C m ih =>
    simp only [MutabilityCtx.subst, MutabilityCtx.renameLoc, ih, CaptureSet.subst_renameLoc]

theorem ModalCtx.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (K : ModalCtx s1) (σ : Subst s1 s2) :
    (K.subst σ).renameLoc π = (K.renameLoc π).subst (σ.renameLoc π) := by
  cases K with
  | mk sep mu =>
    simp only [ModalCtx.subst, ModalCtx.renameLoc,
      SepCtx.subst_renameLoc, MutabilityCtx.subst_renameLoc]

theorem Ty.subst_renameLoc (π : Equiv.Perm Nat) {sort : TySort} {s1 s2 : Sig}
    (T : Ty sort s1) (σ : Subst s1 s2) :
    (T.subst σ).renameLoc π = (T.renameLoc π).subst (σ.renameLoc π) := by
  induction T generalizing s2 with
  | top => rfl
  | tvar x => simp only [Ty.subst, Ty.renameLoc, Subst.renameLoc, PureTy.renameLoc]
  | unit => rfl
  | bool => rfl
  | arrow _ _ _ ih1 ih2 =>
    simp only [Ty.subst, Ty.renameLoc, CaptureSet.subst_renameLoc, ih1, ih2,
      ← Subst.lift_renameLoc]
    rfl
  | poly _ _ _ ih1 ih2 =>
    simp only [Ty.subst, Ty.renameLoc, CaptureSet.subst_renameLoc, ih1, ih2,
      ← Subst.lift_renameLoc]
    rfl
  | cpoly _ _ _ ih =>
    simp only [Ty.subst, Ty.renameLoc, CaptureSet.subst_renameLoc,
      CaptureBound.subst_renameLoc, ih, ← Subst.lift_renameLoc]
    rfl
  | modal _ _ _ ih =>
    simp only [Ty.subst, Ty.renameLoc, CaptureSet.subst_renameLoc,
      ModalCtx.subst_renameLoc, ih]
  | cap _ => simp only [Ty.subst, Ty.renameLoc, CaptureSet.subst_renameLoc]
  | cell _ => simp only [Ty.subst, Ty.renameLoc, CaptureSet.subst_renameLoc]
  | reader _ => simp only [Ty.subst, Ty.renameLoc, CaptureSet.subst_renameLoc]
  | exi _ ih =>
    simp only [Ty.subst, Ty.renameLoc, ih, ← Subst.lift_renameLoc]
    rfl
  | typ _ ih => simp only [Ty.subst, Ty.renameLoc, ih]

theorem PureTy.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (T : PureTy s1) (σ : Subst s1 s2) :
    (T.subst σ).renameLoc π = (T.renameLoc π).subst (σ.renameLoc π) := by
  apply PureTy.eq_of_core
  simp only [PureTy.subst, PureTy.renameLoc, Ty.subst_renameLoc]

/-- `renameLoc` commutes with `subst` (the linchpin): renaming free locations is
    orthogonal to De Bruijn substitution. -/
theorem Exp.subst_renameLoc (π : Equiv.Perm Nat) {s1 s2 : Sig}
    (e : Exp s1) (σ : Subst s1 s2) :
    (e.subst σ).renameLoc π = (e.renameLoc π).subst (σ.renameLoc π) := by
  induction e generalizing s2 with
  | var x => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc]
  | abs _ _ _ ih =>
    simp only [Exp.subst, Exp.renameLoc, CaptureSet.subst_renameLoc, Ty.subst_renameLoc, ih,
      ← Subst.lift_renameLoc]
    rfl
  | tabs _ _ _ ih =>
    simp only [Exp.subst, Exp.renameLoc, CaptureSet.subst_renameLoc, PureTy.subst_renameLoc, ih,
      ← Subst.lift_renameLoc]
    rfl
  | cabs _ _ _ ih =>
    simp only [Exp.subst, Exp.renameLoc, CaptureSet.subst_renameLoc,
      CaptureBound.subst_renameLoc, ih, ← Subst.lift_renameLoc]
    rfl
  | boxed _ _ _ ih => simp only [Exp.subst, Exp.renameLoc, CaptureSet.subst_renameLoc,
      ModalCtx.subst_renameLoc, ih]
  | reader x => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc]
  | alloc x => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc]
  | drop x => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc]
  | pack _ x => simp only [Exp.subst, Exp.renameLoc, CaptureSet.subst_renameLoc,
      Var.subst_renameLoc]
  | app x y => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc]
  | tapp x _ => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc,
      PureTy.subst_renameLoc]
  | capp x _ => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc,
      CaptureSet.subst_renameLoc]
  | unwrap x => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc]
  | letin _ _ ih1 ih2 =>
    simp only [Exp.subst, Exp.renameLoc, ih1, ih2, ← Subst.lift_renameLoc]
    rfl
  | unpack _ _ ih1 ih2 =>
    simp only [Exp.subst, Exp.renameLoc, ih1, ih2, ← Subst.lift_renameLoc]
    rfl
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc]
  | write x y => simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc]
  | cond x _ _ ih1 ih2 =>
    simp only [Exp.subst, Exp.renameLoc, Var.subst_renameLoc, ih1, ih2]
  | par _ _ _ _ ih1 ih2 =>
    simp only [Exp.subst, Exp.renameLoc, CaptureSet.subst_renameLoc, ih1, ih2]

/-- Opening with a location commutes with renaming. -/
theorem Subst.openVar_renameLoc (π : Equiv.Perm Nat) {s : Sig} (y : Nat) :
    (Subst.openVar (s:=s) (.free y)).renameLoc π = Subst.openVar (.free (π y)) := by
  apply Subst.funext
  · intro x; cases x with
    | here => rfl
    | there x0 => rfl
  · intro X; cases X with
    | there X0 => rfl
  · intro C; cases C with
    | there C0 => rfl

/-- Specialised linchpin for opening a value binder with a location. -/
theorem Exp.openVar_renameLoc (π : Equiv.Perm Nat) {s : Sig}
    (e : Exp (s,x)) (y : Nat) :
    (e.subst (Subst.openVar (.free y))).renameLoc π
      = (e.renameLoc π).subst (Subst.openVar (.free (π y))) := by
  rw [Exp.subst_renameLoc, Subst.openVar_renameLoc]

/-- Opening a value binder with an arbitrary variable commutes with renaming. -/
theorem Subst.openVar_var_renameLoc (π : Equiv.Perm Nat) {s : Sig} (x : Var .var s) :
    (Subst.openVar x).renameLoc π = Subst.openVar (x.renameLoc π) := by
  apply Subst.funext
  · intro y; cases y with
    | here => rfl
    | there y0 => rfl
  · intro X; cases X with
    | there X0 => rfl
  · intro C; cases C with
    | there C0 => rfl

/-- Opening a type-variable binder with `U` commutes with renaming. -/
theorem Subst.openTVar_renameLoc (π : Equiv.Perm Nat) {s : Sig} (U : PureTy s) :
    (Subst.openTVar U).renameLoc π = Subst.openTVar (U.renameLoc π) := by
  apply Subst.funext
  · intro x; cases x with
    | there x0 => rfl
  · intro X; cases X with
    | here => rfl
    | there X0 => rfl
  · intro C; cases C with
    | there C0 => rfl

/-- Opening a capture-variable binder with `C` commutes with renaming. -/
theorem Subst.openCVar_renameLoc (π : Equiv.Perm Nat) {s : Sig} (C : CaptureSet s) :
    (Subst.openCVar C).renameLoc π = Subst.openCVar (C.renameLoc π) := by
  apply Subst.funext
  · intro x; cases x with
    | there x0 => rfl
  · intro X; cases X with
    | there X0 => rfl
  · intro C0; cases C0 with
    | here => rfl
    | there C1 => rfl

/-- Opening an existential package commutes with renaming. -/
theorem Subst.unpack_renameLoc (π : Equiv.Perm Nat) {s : Sig} (C : CaptureSet s)
    (x : Var .var s) :
    (Subst.unpack C x).renameLoc π = Subst.unpack (C.renameLoc π) (x.renameLoc π) := by
  apply Subst.funext
  · intro y; cases y with
    | here => rfl
    | there y0 => cases y0 with | there y1 => rfl
  · intro X; cases X with
    | there X0 => cases X0 with | there X1 => rfl
  · intro C0; cases C0 with
    | there C1 => cases C1 with
      | here => rfl
      | there C2 => rfl

theorem Var.WfInHeap.renameLoc {x : Var k s} {h : Heap} (hwf : x.WfInHeap h)
    (π : Equiv.Perm Nat) : (x.renameLoc π).WfInHeap (h.renameLoc π) := by
  cases hwf with
  | wf_bound => exact .wf_bound
  | wf_free hn => exact .wf_free (by rw [Heap.lookup_renameLoc, hn]; rfl)

theorem CaptureSet.WfInHeap.renameLoc {cs : CaptureSet s} {h : Heap} (hwf : cs.WfInHeap h)
    (π : Equiv.Perm Nat) : (cs.renameLoc π).WfInHeap (h.renameLoc π) := by
  induction hwf with
  | wf_empty => exact .wf_empty
  | wf_union _ _ ih1 ih2 => exact .wf_union ih1 ih2
  | wf_var_free hn => exact .wf_var_free (by rw [Heap.lookup_renameLoc, hn]; rfl)
  | wf_var_bound => exact .wf_var_bound
  | wf_cvar => exact .wf_cvar

theorem CaptureBound.WfInHeap.renameLoc {cb : CaptureBound s} {h : Heap} (hwf : cb.WfInHeap h)
    (π : Equiv.Perm Nat) : (cb.renameLoc π).WfInHeap (h.renameLoc π) := by
  cases hwf with
  | wf_unbound => exact .wf_unbound
  | wf_bound hcs => exact .wf_bound (hcs.renameLoc π)

theorem SepCtx.WfInHeap.renameLoc {K : SepCtx s} {h : Heap} (hwf : K.WfInHeap h)
    (π : Equiv.Perm Nat) : (K.renameLoc π).WfInHeap (h.renameLoc π) := by
  induction hwf with
  | wf_empty => exact .wf_empty
  | wf_cons _ hC ih => exact .wf_cons ih (hC.renameLoc π)

theorem MutabilityCtx.WfInHeap.renameLoc {K : MutabilityCtx s} {h : Heap} (hwf : K.WfInHeap h)
    (π : Equiv.Perm Nat) : (K.renameLoc π).WfInHeap (h.renameLoc π) := by
  induction hwf with
  | wf_empty => exact .wf_empty
  | wf_cons _ hC ih => exact .wf_cons ih (hC.renameLoc π)

theorem ModalCtx.WfInHeap.renameLoc {K : ModalCtx s} {h : Heap} (hwf : K.WfInHeap h)
    (π : Equiv.Perm Nat) : (K.renameLoc π).WfInHeap (h.renameLoc π) :=
  ⟨hwf.sep.renameLoc π, hwf.mutability.renameLoc π⟩

theorem Ty.WfInHeap.renameLoc {T : Ty sort s} {h : Heap} (hwf : T.WfInHeap h)
    (π : Equiv.Perm Nat) : (T.renameLoc π).WfInHeap (h.renameLoc π) := by
  induction hwf with
  | wf_top => exact .wf_top
  | wf_tvar => exact .wf_tvar
  | wf_unit => exact .wf_unit
  | wf_bool => exact .wf_bool
  | wf_arrow _ hcs _ ih1 ih2 => exact .wf_arrow ih1 (hcs.renameLoc π) ih2
  | wf_poly _ hcs _ ih1 ih2 => exact .wf_poly ih1 (hcs.renameLoc π) ih2
  | wf_cpoly hcb hcs _ ih => exact .wf_cpoly (hcb.renameLoc π) (hcs.renameLoc π) ih
  | wf_modal hcs hΨ _ ih => exact .wf_modal (hcs.renameLoc π) (hΨ.renameLoc π) ih
  | wf_cap hcs => exact .wf_cap (hcs.renameLoc π)
  | wf_cell hcs => exact .wf_cell (hcs.renameLoc π)
  | wf_reader hcs => exact .wf_reader (hcs.renameLoc π)
  | wf_exi _ ih => exact .wf_exi ih
  | wf_typ _ ih => exact .wf_typ ih

theorem PureTy.WfInHeap.renameLoc {T : PureTy s} {h : Heap} (hwf : T.WfInHeap h)
    (π : Equiv.Perm Nat) : (T.renameLoc π).WfInHeap (h.renameLoc π) :=
  Ty.WfInHeap.renameLoc hwf π

/-- Expression well-formedness is equivariant. -/
theorem Exp.WfInHeap.renameLoc {e : Exp s} {h : Heap} (hwf : e.WfInHeap h)
    (π : Equiv.Perm Nat) : (e.renameLoc π).WfInHeap (h.renameLoc π) := by
  induction hwf with
  | wf_var hx => exact .wf_var (hx.renameLoc π)
  | wf_abs hcs hT _ ih => exact .wf_abs (hcs.renameLoc π) (hT.renameLoc π) ih
  | wf_tabs hcs hT _ ih => exact .wf_tabs (hcs.renameLoc π) (hT.renameLoc π) ih
  | wf_cabs hcs hcb _ ih => exact .wf_cabs (hcs.renameLoc π) (hcb.renameLoc π) ih
  | wf_boxed hcs hΨ _ ih => exact .wf_boxed (hcs.renameLoc π) (hΨ.renameLoc π) ih
  | wf_reader hx => exact .wf_reader (hx.renameLoc π)
  | wf_alloc hx => exact .wf_alloc (hx.renameLoc π)
  | wf_drop hx => exact .wf_drop (hx.renameLoc π)
  | wf_pack hcs hx => exact .wf_pack (hcs.renameLoc π) (hx.renameLoc π)
  | wf_app hx hy => exact .wf_app (hx.renameLoc π) (hy.renameLoc π)
  | wf_tapp hx hT => exact .wf_tapp (hx.renameLoc π) (hT.renameLoc π)
  | wf_capp hx hcs => exact .wf_capp (hx.renameLoc π) (hcs.renameLoc π)
  | wf_unwrap hx => exact .wf_unwrap (hx.renameLoc π)
  | wf_letin _ _ ih1 ih2 => exact .wf_letin ih1 ih2
  | wf_unpack _ _ ih1 ih2 => exact .wf_unpack ih1 ih2
  | wf_unit => exact .wf_unit
  | wf_btrue => exact .wf_btrue
  | wf_bfalse => exact .wf_bfalse
  | wf_read hx => exact .wf_read (hx.renameLoc π)
  | wf_write hx hy => exact .wf_write (hx.renameLoc π) (hy.renameLoc π)
  | wf_cond hx _ _ ih2 ih3 => exact .wf_cond (hx.renameLoc π) ih2 ih3
  | wf_par hC1 hC2 _ _ ih1 ih2 => exact .wf_par (hC1.renameLoc π) (hC2.renameLoc π) ih1 ih2

/-- A renamed lookup of a value cell comes from a value cell at the preimage. -/
theorem Heap.renameLoc_lookup_val {h : Heap} {π : Equiv.Perm Nat} {l : Nat} {hv : HeapVal}
    (hlk : (h.renameLoc π) l = some (.val hv)) :
    ∃ hv0, h (π.symm l) = some (.val hv0) ∧ hv = hv0.renameLoc π := by
  unfold Heap.renameLoc at hlk
  cases hc : h (π.symm l) with
  | none => rw [hc] at hlk; simp at hlk
  | some c =>
    rw [hc] at hlk
    cases c with
    | val hv0 =>
      refine ⟨hv0, rfl, ?_⟩
      simp only [Option.map_some, Cell.renameLoc, Option.some.injEq, Cell.val.injEq] at hlk
      exact hlk.symm
    | capability ci => simp [Cell.renameLoc] at hlk
    | masked => simp [Cell.renameLoc] at hlk

/-- Heap well-formedness is equivariant. -/
theorem Heap.WfHeap.renameLoc {h : Heap} (hwf : h.WfHeap) (π : Equiv.Perm Nat) :
    (h.renameLoc π).WfHeap := by
  constructor
  · intro l hv hlk
    obtain ⟨hv0, hc, rfl⟩ := Heap.renameLoc_lookup_val hlk
    simpa only [HeapVal.renameLoc] using (hwf.wf_val (π.symm l) hv0 hc).renameLoc π
  · intro l v hv R hlk
    obtain ⟨hv0, hc, hve⟩ := Heap.renameLoc_lookup_val hlk
    cases hv0 with
    | mk v0 hv0val R0 =>
      have hvu : v = v0.renameLoc π := by
        simpa only [HeapVal.renameLoc] using congrArg HeapVal.unwrap hve
      have hvr : R = R0.renameLoc π := by
        simpa only [HeapVal.renameLoc] using congrArg HeapVal.reachability hve
      subst hvu; subst hvr
      rw [hwf.wf_reach (π.symm l) v0 hv0val R0 hc]
      exact (compute_reachability_renameLoc π h v0 hv0val).symm
  · intro l v hv R hlk mu l' hmem
    obtain ⟨hv0, hc, hve⟩ := Heap.renameLoc_lookup_val hlk
    cases hv0 with
    | mk v0 hv0val R0 =>
      have hvr : R = R0.renameLoc π := by
        simpa only [HeapVal.renameLoc] using congrArg HeapVal.reachability hve
      subst hvr
      rw [show l' = π (π.symm l') from (π.apply_symm_apply l').symm] at hmem ⊢
      rw [CapabilitySet.hasmem_renameLoc] at hmem
      have hdne := hwf.wf_reach_dom (π.symm l) v0 hv0val R0 hc mu (π.symm l') hmem
      rw [Heap.lookup_renameLoc]
      cases hh : h (π.symm l') with
      | none => exact absurd hh hdne
      | some c => simp

/-- A renamed heap has finite domain (the image of the original domain). -/
theorem Heap.HasFinDom.renameLoc {h : Heap} {dom : Finset Nat}
    (hdom : h.HasFinDom dom) (π : Equiv.Perm Nat) :
    (h.renameLoc π).HasFinDom (dom.image π) := by
  intro l'
  have key : (h.renameLoc π) l' ≠ none ↔ h (π.symm l') ≠ none := by
    unfold Heap.renameLoc
    cases h (π.symm l') <;> simp
  rw [key, hdom (π.symm l')]
  constructor
  · intro hm; exact Finset.mem_image.mpr ⟨π.symm l', hm, π.apply_symm_apply l'⟩
  · intro hm
    obtain ⟨b, hb, hbl⟩ := Finset.mem_image.mp hm
    rw [← hbl, Equiv.symm_apply_apply]; exact hb

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

/-- A renamed capability cell is looked up at the renamed location. -/
theorem Memory.lookup_cap_renameLoc {m : Memory} {l : Nat} {ci : CapabilityInfo}
    (h : m.lookup l = some (.capability ci)) (π : Equiv.Perm Nat) :
    (m.renameLoc π).lookup (π l) = some (.capability ci) := by
  rw [Memory.lookup_renameLoc, h]; rfl

/-- A renamed value cell is looked up at the renamed location (value renamed). -/
theorem Memory.lookup_val_renameLoc {m : Memory} {l : Nat} {hv : HeapVal}
    (h : m.lookup l = some (.val hv)) (π : Equiv.Perm Nat) :
    (m.renameLoc π).lookup (π l) = some (.val (hv.renameLoc π)) := by
  rw [Memory.lookup_renameLoc, h]; rfl

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

theorem CaptureBound.renameLoc_id {cb : CaptureBound s} :
    cb.renameLoc (Equiv.refl Nat) = cb := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CaptureBound.renameLoc, CaptureSet.renameLoc_id]

theorem SepCtx.renameLoc_id {K : SepCtx s} : K.renameLoc (Equiv.refl Nat) = K := by
  induction K with
  | empty => rfl
  | cons K C ih => simp only [SepCtx.renameLoc, ih, CaptureSet.renameLoc_id]

theorem MutabilityCtx.renameLoc_id {K : MutabilityCtx s} : K.renameLoc (Equiv.refl Nat) = K := by
  induction K with
  | empty => rfl
  | cons K C m ih => simp only [MutabilityCtx.renameLoc, ih, CaptureSet.renameLoc_id]

theorem ModalCtx.renameLoc_id {K : ModalCtx s} : K.renameLoc (Equiv.refl Nat) = K := by
  cases K with
  | mk sep mu =>
    simp only [ModalCtx.renameLoc, SepCtx.renameLoc_id, MutabilityCtx.renameLoc_id]

theorem Ty.renameLoc_id {T : Ty sort s} : T.renameLoc (Equiv.refl Nat) = T := by
  induction T with
  | top => rfl
  | tvar x => rfl
  | unit => rfl
  | bool => rfl
  | arrow _ _ _ ih1 ih2 => simp only [Ty.renameLoc, CaptureSet.renameLoc_id, ih1, ih2]
  | poly _ _ _ ih1 ih2 => simp only [Ty.renameLoc, CaptureSet.renameLoc_id, ih1, ih2]
  | cpoly _ _ _ ih =>
    simp only [Ty.renameLoc, CaptureSet.renameLoc_id, CaptureBound.renameLoc_id, ih]
  | modal _ _ _ ih =>
    simp only [Ty.renameLoc, CaptureSet.renameLoc_id, ModalCtx.renameLoc_id, ih]
  | cap _ => simp only [Ty.renameLoc, CaptureSet.renameLoc_id]
  | cell _ => simp only [Ty.renameLoc, CaptureSet.renameLoc_id]
  | reader _ => simp only [Ty.renameLoc, CaptureSet.renameLoc_id]
  | exi _ ih => simp only [Ty.renameLoc, ih]
  | typ _ ih => simp only [Ty.renameLoc, ih]

theorem PureTy.renameLoc_id {T : PureTy s} : T.renameLoc (Equiv.refl Nat) = T := by
  apply PureTy.eq_of_core
  simp only [PureTy.renameLoc, Ty.renameLoc_id]

/-- `Exp.renameLoc` by the identity permutation is the identity. -/
theorem Exp.renameLoc_id {e : Exp s} : e.renameLoc (Equiv.refl Nat) = e := by
  induction e with
  | var x => simp only [Exp.renameLoc, Var.renameLoc_id]
  | abs _ _ _ ih => simp only [Exp.renameLoc, CaptureSet.renameLoc_id, Ty.renameLoc_id, ih]
  | tabs _ _ _ ih => simp only [Exp.renameLoc, CaptureSet.renameLoc_id, PureTy.renameLoc_id, ih]
  | cabs _ _ _ ih =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_id, CaptureBound.renameLoc_id, ih]
  | boxed _ _ _ ih =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_id, ModalCtx.renameLoc_id, ih]
  | reader x => simp only [Exp.renameLoc, Var.renameLoc_id]
  | alloc x => simp only [Exp.renameLoc, Var.renameLoc_id]
  | drop x => simp only [Exp.renameLoc, Var.renameLoc_id]
  | pack _ x => simp only [Exp.renameLoc, CaptureSet.renameLoc_id, Var.renameLoc_id]
  | app x y => simp only [Exp.renameLoc, Var.renameLoc_id]
  | tapp x _ => simp only [Exp.renameLoc, Var.renameLoc_id, PureTy.renameLoc_id]
  | capp x _ => simp only [Exp.renameLoc, Var.renameLoc_id, CaptureSet.renameLoc_id]
  | unwrap x => simp only [Exp.renameLoc, Var.renameLoc_id]
  | letin _ _ ih1 ih2 => simp only [Exp.renameLoc, ih1, ih2]
  | unpack _ _ ih1 ih2 => simp only [Exp.renameLoc, ih1, ih2]
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x => simp only [Exp.renameLoc, Var.renameLoc_id]
  | write x y => simp only [Exp.renameLoc, Var.renameLoc_id]
  | cond x _ _ ih1 ih2 => simp only [Exp.renameLoc, Var.renameLoc_id, ih1, ih2]
  | par _ _ _ _ ih1 ih2 => simp only [Exp.renameLoc, CaptureSet.renameLoc_id, ih1, ih2]

/-- Two heap values are equal once their value and reachability agree. -/
theorem HeapVal.eq_of {hv1 hv2 : HeapVal}
    (hu : hv1.unwrap = hv2.unwrap) (hr : hv1.reachability = hv2.reachability) : hv1 = hv2 := by
  cases hv1; cases hv2; cases hu; cases hr; rfl

theorem HeapVal.renameLoc_id {hv : HeapVal} : hv.renameLoc (Equiv.refl Nat) = hv := by
  apply HeapVal.eq_of <;>
    simp only [HeapVal.renameLoc, Exp.renameLoc_id, CapabilitySet.renameLoc_id]

theorem Cell.renameLoc_id {c : Cell} : c.renameLoc (Equiv.refl Nat) = c := by
  cases c with
  | val hv => simp only [Cell.renameLoc, HeapVal.renameLoc_id]
  | capability ci => rfl
  | masked => rfl

theorem Heap.renameLoc_id {h : Heap} : h.renameLoc (Equiv.refl Nat) = h := by
  funext l
  simp only [Heap.renameLoc, Equiv.refl_symm, Equiv.refl_apply]
  cases h l with
  | none => rfl
  | some c => simp only [Option.map_some, Cell.renameLoc_id]

/-- Two memories are equal once their heaps agree (the `wf`/`findom` fields are Props). -/
theorem Memory.eq_of_heap {m1 m2 : Memory} (h : m1.heap = m2.heap) : m1 = m2 := by
  cases m1; cases m2; cases h; rfl

theorem Memory.renameLoc_id {m : Memory} : m.renameLoc (Equiv.refl Nat) = m := by
  apply Memory.eq_of_heap
  exact Heap.renameLoc_id

theorem Var.renameLoc_comp {x : Var k s} {π ρ : Equiv.Perm Nat} :
    (x.renameLoc π).renameLoc ρ = x.renameLoc (π.trans ρ) := by
  cases x with
  | bound b => rfl
  | free n => simp only [Var.renameLoc, Equiv.trans_apply]

theorem CaptureSet.renameLoc_comp {cs : CaptureSet s} {π ρ : Equiv.Perm Nat} :
    (cs.renameLoc π).renameLoc ρ = cs.renameLoc (π.trans ρ) := by
  induction cs with
  | empty => rfl
  | union _ _ ih1 ih2 => simp only [CaptureSet.renameLoc, ih1, ih2]
  | var m x => simp only [CaptureSet.renameLoc, Var.renameLoc_comp]
  | cvar m x => rfl

theorem CaptureBound.renameLoc_comp {cb : CaptureBound s} {π ρ : Equiv.Perm Nat} :
    (cb.renameLoc π).renameLoc ρ = cb.renameLoc (π.trans ρ) := by
  cases cb with
  | unbound => rfl
  | bound cs => simp only [CaptureBound.renameLoc, CaptureSet.renameLoc_comp]

theorem SepCtx.renameLoc_comp {K : SepCtx s} {π ρ : Equiv.Perm Nat} :
    (K.renameLoc π).renameLoc ρ = K.renameLoc (π.trans ρ) := by
  induction K with
  | empty => rfl
  | cons K C ih => simp only [SepCtx.renameLoc, ih, CaptureSet.renameLoc_comp]

theorem MutabilityCtx.renameLoc_comp {K : MutabilityCtx s} {π ρ : Equiv.Perm Nat} :
    (K.renameLoc π).renameLoc ρ = K.renameLoc (π.trans ρ) := by
  induction K with
  | empty => rfl
  | cons K C m ih => simp only [MutabilityCtx.renameLoc, ih, CaptureSet.renameLoc_comp]

theorem ModalCtx.renameLoc_comp {K : ModalCtx s} {π ρ : Equiv.Perm Nat} :
    (K.renameLoc π).renameLoc ρ = K.renameLoc (π.trans ρ) := by
  cases K with
  | mk sep mu =>
    simp only [ModalCtx.renameLoc, SepCtx.renameLoc_comp, MutabilityCtx.renameLoc_comp]

theorem Ty.renameLoc_comp {T : Ty sort s} {π ρ : Equiv.Perm Nat} :
    (T.renameLoc π).renameLoc ρ = T.renameLoc (π.trans ρ) := by
  induction T with
  | top => rfl
  | tvar x => rfl
  | unit => rfl
  | bool => rfl
  | arrow _ _ _ ih1 ih2 => simp only [Ty.renameLoc, CaptureSet.renameLoc_comp, ih1, ih2]
  | poly _ _ _ ih1 ih2 => simp only [Ty.renameLoc, CaptureSet.renameLoc_comp, ih1, ih2]
  | cpoly _ _ _ ih =>
    simp only [Ty.renameLoc, CaptureSet.renameLoc_comp, CaptureBound.renameLoc_comp, ih]
  | modal _ _ _ ih =>
    simp only [Ty.renameLoc, CaptureSet.renameLoc_comp, ModalCtx.renameLoc_comp, ih]
  | cap _ => simp only [Ty.renameLoc, CaptureSet.renameLoc_comp]
  | cell _ => simp only [Ty.renameLoc, CaptureSet.renameLoc_comp]
  | reader _ => simp only [Ty.renameLoc, CaptureSet.renameLoc_comp]
  | exi _ ih => simp only [Ty.renameLoc, ih]
  | typ _ ih => simp only [Ty.renameLoc, ih]

theorem PureTy.renameLoc_comp {T : PureTy s} {π ρ : Equiv.Perm Nat} :
    (T.renameLoc π).renameLoc ρ = T.renameLoc (π.trans ρ) := by
  apply PureTy.eq_of_core
  simp only [PureTy.renameLoc, Ty.renameLoc_comp]

theorem Exp.renameLoc_comp {e : Exp s} {π ρ : Equiv.Perm Nat} :
    (e.renameLoc π).renameLoc ρ = e.renameLoc (π.trans ρ) := by
  induction e with
  | var x => simp only [Exp.renameLoc, Var.renameLoc_comp]
  | abs _ _ _ ih => simp only [Exp.renameLoc, CaptureSet.renameLoc_comp, Ty.renameLoc_comp, ih]
  | tabs _ _ _ ih => simp only [Exp.renameLoc, CaptureSet.renameLoc_comp, PureTy.renameLoc_comp, ih]
  | cabs _ _ _ ih =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_comp, CaptureBound.renameLoc_comp, ih]
  | boxed _ _ _ ih =>
    simp only [Exp.renameLoc, CaptureSet.renameLoc_comp, ModalCtx.renameLoc_comp, ih]
  | reader x => simp only [Exp.renameLoc, Var.renameLoc_comp]
  | alloc x => simp only [Exp.renameLoc, Var.renameLoc_comp]
  | drop x => simp only [Exp.renameLoc, Var.renameLoc_comp]
  | pack _ x => simp only [Exp.renameLoc, CaptureSet.renameLoc_comp, Var.renameLoc_comp]
  | app x y => simp only [Exp.renameLoc, Var.renameLoc_comp]
  | tapp x _ => simp only [Exp.renameLoc, Var.renameLoc_comp, PureTy.renameLoc_comp]
  | capp x _ => simp only [Exp.renameLoc, Var.renameLoc_comp, CaptureSet.renameLoc_comp]
  | unwrap x => simp only [Exp.renameLoc, Var.renameLoc_comp]
  | letin _ _ ih1 ih2 => simp only [Exp.renameLoc, ih1, ih2]
  | unpack _ _ ih1 ih2 => simp only [Exp.renameLoc, ih1, ih2]
  | unit => rfl
  | btrue => rfl
  | bfalse => rfl
  | read x => simp only [Exp.renameLoc, Var.renameLoc_comp]
  | write x y => simp only [Exp.renameLoc, Var.renameLoc_comp]
  | cond x _ _ ih1 ih2 => simp only [Exp.renameLoc, Var.renameLoc_comp, ih1, ih2]
  | par _ _ _ _ ih1 ih2 => simp only [Exp.renameLoc, CaptureSet.renameLoc_comp, ih1, ih2]

theorem CapabilitySet.renameLoc_comp {C : CapabilitySet} {π ρ : Equiv.Perm Nat} :
    (C.renameLoc π).renameLoc ρ = C.renameLoc (π.trans ρ) := by
  induction C with
  | empty => rfl
  | cap m l => simp only [CapabilitySet.renameLoc, Equiv.trans_apply]
  | union _ _ ih1 ih2 => simp only [CapabilitySet.renameLoc, ih1, ih2]

theorem HeapVal.renameLoc_comp {hv : HeapVal} {π ρ : Equiv.Perm Nat} :
    (hv.renameLoc π).renameLoc ρ = hv.renameLoc (π.trans ρ) := by
  apply HeapVal.eq_of <;>
    simp only [HeapVal.renameLoc, Exp.renameLoc_comp, CapabilitySet.renameLoc_comp]

theorem Cell.renameLoc_comp {c : Cell} {π ρ : Equiv.Perm Nat} :
    (c.renameLoc π).renameLoc ρ = c.renameLoc (π.trans ρ) := by
  cases c with
  | val hv => simp only [Cell.renameLoc, HeapVal.renameLoc_comp]
  | capability ci => rfl
  | masked => rfl

theorem Heap.renameLoc_comp {h : Heap} {π ρ : Equiv.Perm Nat} :
    (h.renameLoc π).renameLoc ρ = h.renameLoc (π.trans ρ) := by
  funext l
  simp only [Heap.renameLoc, Option.map_map, Equiv.symm_trans_apply]
  cases h (π.symm (ρ.symm l)) with
  | none => rfl
  | some c => simp only [Option.map_some, Function.comp_apply, Cell.renameLoc_comp]

theorem Memory.renameLoc_comp {m : Memory} {π ρ : Equiv.Perm Nat} :
    (m.renameLoc π).renameLoc ρ = m.renameLoc (π.trans ρ) := by
  apply Memory.eq_of_heap
  exact Heap.renameLoc_comp

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
  ⟨Equiv.refl Nat, Memory.renameLoc_id.symm⟩

theorem Memory.Iso.symm {m1 m2 : Memory} (h : m1.Iso m2) : m2.Iso m1 := by
  obtain ⟨π, rfl⟩ := h
  exact ⟨π.symm, by rw [Memory.renameLoc_comp, Equiv.self_trans_symm, Memory.renameLoc_id]⟩

theorem Memory.Iso.trans {m1 m2 m3 : Memory} (h1 : m1.Iso m2) (h2 : m2.Iso m3) :
    m1.Iso m3 := by
  obtain ⟨π, rfl⟩ := h1
  obtain ⟨ρ, rfl⟩ := h2
  exact ⟨π.trans ρ, Memory.renameLoc_comp⟩

/-! ## Operational equivariance (the payoff)

  Every operational relation is closed under simultaneous location renaming.
  These are the theorems the Church–Rosser proof consumes (to resolve the
  fresh-name clash by renaming one side of a divergence). -/

/-! ### Helper lemmas for the operational equivariance proofs -/

/-- Trace renaming distributes over concatenation (it is a `List.map`). -/
theorem Trace.renameLoc_append (π : Equiv.Perm Nat) (t1 t2 : Trace) :
    (t1 ++ t2).renameLoc π = t1.renameLoc π ++ t2.renameLoc π := by
  simp only [Trace.renameLoc, List.map_append]

/-- Freshness is transported by `π`. -/
theorem Heap.fresh_renameLoc {h : Heap} {l : Nat} (hfresh : h l = none)
    (π : Equiv.Perm Nat) : (h.renameLoc π) (π l) = none := by
  rw [Heap.lookup_renameLoc, hfresh]; rfl

/-- Memory freshness is transported by `π`. -/
theorem Memory.fresh_renameLoc {m : Memory} {l : Nat} (hfresh : m.heap l = none)
    (π : Equiv.Perm Nat) : (m.renameLoc π).heap (π l) = none :=
  Heap.fresh_renameLoc hfresh π

/-- `extend_mcell` commutes with heap renaming. -/
theorem Heap.extend_mcell_renameLoc (π : Equiv.Perm Nat) (h : Heap) (l : Nat) (b : Bool) :
    (h.extend_mcell l b).renameLoc π = (h.renameLoc π).extend_mcell (π l) b := by
  funext l'
  simp only [Heap.renameLoc, Heap.extend_mcell]
  by_cases hl : l' = π l
  · subst hl
    rw [Equiv.symm_apply_apply, if_pos rfl, if_pos rfl]
    rfl
  · rw [if_neg hl]
    rw [if_neg (fun hc : π.symm l' = l => hl (by rw [← hc, Equiv.apply_symm_apply]))]

/-- `update_cell` with a capability cell commutes with heap renaming. -/
theorem Heap.update_cell_cap_renameLoc (π : Equiv.Perm Nat) (h : Heap) (l : Nat)
    (ci : CapabilityInfo) :
    (h.update_cell l (.capability ci)).renameLoc π
      = (h.renameLoc π).update_cell (π l) (.capability ci) := by
  funext l'
  simp only [Heap.renameLoc, Heap.update_cell]
  by_cases hl : l' = π l
  · subst hl
    rw [Equiv.symm_apply_apply, if_pos rfl, if_pos rfl]
    rfl
  · rw [if_neg hl]
    rw [if_neg (fun hc : π.symm l' = l => hl (by rw [← hc, Equiv.apply_symm_apply]))]

/-- `extend` (with a heap value) commutes with heap renaming. -/
theorem Heap.extend_renameLoc (π : Equiv.Perm Nat) (h : Heap) (l : Nat) (v : HeapVal) :
    (h.extend l v).renameLoc π = (h.renameLoc π).extend (π l) (v.renameLoc π) := by
  funext l'
  simp only [Heap.renameLoc, Heap.extend]
  by_cases hl : l' = π l
  · subst hl
    rw [Equiv.symm_apply_apply, if_pos rfl, if_pos rfl]
    rfl
  · rw [if_neg hl]
    rw [if_neg (fun hc : π.symm l' = l => hl (by rw [← hc, Equiv.apply_symm_apply]))]

/-- `extend_mcell` commutes with memory renaming. -/
theorem Memory.extend_mcell_renameLoc (π : Equiv.Perm Nat) (m : Memory) (l : Nat) (b : Bool)
    (hfresh : m.heap l = none) :
    (m.extend_mcell l b hfresh).renameLoc π
      = (m.renameLoc π).extend_mcell (π l) b (Memory.fresh_renameLoc hfresh π) := by
  apply Memory.eq_of_heap
  exact Heap.extend_mcell_renameLoc π m.heap l b

/-- `update_mcell` commutes with memory renaming. -/
theorem Memory.update_mcell_renameLoc (π : Equiv.Perm Nat) (m : Memory) (l : Nat) (b : Bool)
    (ℓ : Liveness) (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 ℓ)))
    (hexists' : ∃ b0, (m.renameLoc π).heap (π l) = some (.capability (.mcell b0 ℓ))) :
    (m.update_mcell l b ℓ hexists).renameLoc π
      = (m.renameLoc π).update_mcell (π l) b ℓ hexists' := by
  apply Memory.eq_of_heap
  exact Heap.update_cell_cap_renameLoc π m.heap l (.mcell b ℓ)

/-- `drop_mcell` commutes with memory renaming. -/
theorem Memory.drop_mcell_renameLoc (π : Equiv.Perm Nat) (m : Memory) (l : Nat)
    (hexists : ∃ b0, m.heap l = some (.capability (.mcell b0 .live)))
    (hexists' : ∃ b0, (m.renameLoc π).heap (π l) = some (.capability (.mcell b0 .live))) :
    (m.drop_mcell l hexists).renameLoc π = (m.renameLoc π).drop_mcell (π l) hexists' := by
  apply Memory.eq_of_heap
  exact Heap.update_cell_cap_renameLoc π m.heap l (.mcell false .dead)

/-- The reachability set used by `step_lift` transports through `π`. -/
theorem compute_reachability_heap_renameLoc (π : Equiv.Perm Nat) (m : Memory)
    (v : Exp {}) (hv : v.IsSimpleVal) :
    compute_reachability (m.renameLoc π).heap (v.renameLoc π) (hv.renameLoc π)
      = (compute_reachability m.heap v hv).renameLoc π :=
  compute_reachability_renameLoc π m.heap v hv

/-- The `extend` used by `step_lift` (storing a freshly computed reachability)
    commutes with memory renaming, transporting both value and reachability. -/
theorem Memory.extend_compute_renameLoc (π : Equiv.Perm Nat) (m : Memory) (l : Nat)
    (v : Exp {}) (hv : v.IsSimpleVal)
    (hwf : Exp.WfInHeap v m.heap) (hfresh : m.heap l = none)
    (hwf' : Exp.WfInHeap (v.renameLoc π) (m.renameLoc π).heap) :
    (m.extend l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl hfresh).renameLoc π
      = (m.renameLoc π).extend (π l)
          ⟨v.renameLoc π, hv.renameLoc π,
            compute_reachability (m.renameLoc π).heap (v.renameLoc π) (hv.renameLoc π)⟩
          hwf' rfl (Memory.fresh_renameLoc hfresh π) := by
  apply Memory.eq_of_heap
  change (m.heap.extend l ⟨v, hv, compute_reachability m.heap v hv⟩).renameLoc π
    = (m.heap.renameLoc π).extend (π l) _
  rw [Heap.extend_renameLoc π m.heap l ⟨v, hv, compute_reachability m.heap v hv⟩]
  congr 1
  exact HeapVal.eq_of rfl (compute_reachability_renameLoc π m.heap v hv).symm

/-- The `extend_val` used by `bs_letin_val` commutes with memory renaming,
    transporting both value and freshly computed reachability. -/
theorem Memory.extend_val_compute_renameLoc (π : Equiv.Perm Nat) (m : Memory) (l : Nat)
    (v : Exp {}) (hv : v.IsSimpleVal)
    (hwf : Exp.WfInHeap v m.heap) (hfresh : m.lookup l = none)
    (hwf' : Exp.WfInHeap (v.renameLoc π) (m.renameLoc π).heap) :
    (m.extend_val l ⟨v, hv, compute_reachability m.heap v hv⟩ hwf rfl hfresh).renameLoc π
      = (m.renameLoc π).extend_val (π l)
          ⟨v.renameLoc π, hv.renameLoc π,
            compute_reachability (m.renameLoc π).heap (v.renameLoc π) (hv.renameLoc π)⟩
          hwf' rfl (Memory.fresh_renameLoc hfresh π) := by
  apply Memory.eq_of_heap
  change (m.heap.extend l ⟨v, hv, compute_reachability m.heap v hv⟩).renameLoc π
    = (m.heap.renameLoc π).extend (π l) _
  rw [Heap.extend_renameLoc π m.heap l ⟨v, hv, compute_reachability m.heap v hv⟩]
  congr 1
  exact HeapVal.eq_of rfl (compute_reachability_renameLoc π m.heap v hv).symm

/-- `extend` commutes with memory renaming, transporting the value. -/
theorem Memory.extend_renameLoc (π : Equiv.Perm Nat) (m : Memory) (l : Nat) (v : HeapVal)
    (hwf : Exp.WfInHeap v.unwrap m.heap)
    (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
    (hfresh : m.heap l = none)
    (hwf' : Exp.WfInHeap (v.renameLoc π).unwrap (m.renameLoc π).heap)
    (hreach' : (v.renameLoc π).reachability
      = compute_reachability (m.renameLoc π).heap (v.renameLoc π).unwrap (v.renameLoc π).isVal) :
    (m.extend l v hwf hreach hfresh).renameLoc π
      = (m.renameLoc π).extend (π l) (v.renameLoc π) hwf' hreach'
          (Memory.fresh_renameLoc hfresh π) := by
  apply Memory.eq_of_heap
  exact Heap.extend_renameLoc π m.heap l v

/-- `extend_val` commutes with memory renaming, transporting the value. -/
theorem Memory.extend_val_renameLoc (π : Equiv.Perm Nat) (m : Memory) (l : Nat) (v : HeapVal)
    (hwf : Exp.WfInHeap v.unwrap m.heap)
    (hreach : v.reachability = compute_reachability m.heap v.unwrap v.isVal)
    (hfresh : m.heap l = none)
    (hwf' : Exp.WfInHeap (v.renameLoc π).unwrap (m.renameLoc π).heap)
    (hreach' : (v.renameLoc π).reachability
      = compute_reachability (m.renameLoc π).heap (v.renameLoc π).unwrap (v.renameLoc π).isVal) :
    (m.extend_val l v hwf hreach hfresh).renameLoc π
      = (m.renameLoc π).extend_val (π l) (v.renameLoc π) hwf' hreach'
          (Memory.fresh_renameLoc hfresh π) := by
  apply Memory.eq_of_heap
  exact Heap.extend_renameLoc π m.heap l v

/-- `growByAllocs` commutes with renaming on both the set and the trace. -/
theorem CaptureSet.growByAllocs_renameLoc (π : Equiv.Perm Nat) (C : CaptureSet {})
    (t : Trace) :
    (C.growByAllocs t).renameLoc π = (C.renameLoc π).growByAllocs (t.renameLoc π) := by
  induction t generalizing C with
  | nil => rfl
  | cons it t ih =>
    cases it with
    | alloc l =>
      simp only [CaptureSet.growByAllocs, Trace.renameLoc, List.map_cons, TraceItem.renameLoc, ih]
      rfl
    | access mu l =>
      simp only [CaptureSet.growByAllocs, Trace.renameLoc, List.map_cons, TraceItem.renameLoc, ih]
    | dealloc l =>
      simp only [CaptureSet.growByAllocs, Trace.renameLoc, List.map_cons, TraceItem.renameLoc, ih]

/-- `CaptureSet.reachability` commutes with renaming. -/
theorem CaptureSet.reachability_renameLoc (π : Equiv.Perm Nat) (C : CaptureSet {}) (m : Memory) :
    (C.reachability m).renameLoc π = (C.renameLoc π).reachability (m.renameLoc π) := by
  induction C with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change (CapabilitySet.union _ _).renameLoc π = CapabilitySet.union _ _
    simp only [CapabilitySet.renameLoc]
    rw [ih1, ih2]
  | var m' x =>
    cases x with
    | bound b => cases b
    | free loc =>
      change (CapabilitySet.applyAccess m' (reachability_of_loc m.heap loc)).renameLoc π
        = CapabilitySet.applyAccess m' (reachability_of_loc (m.heap.renameLoc π) (π loc))
      rw [CapabilitySet.applyAccess_renameLoc, reachability_of_loc_renameLoc]
  | cvar m' x => cases x

/-- Coverage in a renamed capability set tracks the renamed location. -/
theorem CapabilitySet.covers_renameLoc (π : Equiv.Perm Nat) {C : CapabilitySet}
    {m : CapMode} {l : Nat} :
    (C.renameLoc π).covers m (π l) ↔ C.covers m l := by
  induction C with
  | empty =>
    exact ⟨fun h => (CapabilitySet.not_covers_empty h).elim,
           fun h => (CapabilitySet.not_covers_empty h).elim⟩
  | cap m' l' =>
    simp only [CapabilitySet.renameLoc, CapabilitySet.covers_cap_iff]
    constructor
    · rintro ⟨hle, hl⟩; exact ⟨hle, π.injective hl⟩
    · rintro ⟨hle, rfl⟩; exact ⟨hle, rfl⟩
  | union C1 C2 ih1 ih2 =>
    constructor
    · intro hh
      cases hh with
      | left h => exact .left (ih1.mp h)
      | right h => exact .right (ih2.mp h)
    · intro hh
      cases hh with
      | left h => exact .left (ih1.mpr h)
      | right h => exact .right (ih2.mpr h)

/-- `TraceOkFrom` is equivariant: rename the budget, the allocated set, and the
    trace by the same `π`. -/
theorem TraceOkFrom.renameLoc {C : CapabilitySet} {A : List Nat} {t : Trace}
    (h : TraceOkFrom C A t) (π : Equiv.Perm Nat) :
    TraceOkFrom (C.renameLoc π) (A.map π) (t.renameLoc π) := by
  induction h with
  | nil => exact TraceOkFrom.nil
  | alloc _ ih =>
    exact TraceOkFrom.alloc ih
  | access hcond _ ih =>
    refine TraceOkFrom.access ?_ ih
    rcases hcond with hcov | hin
    · exact Or.inl ((CapabilitySet.covers_renameLoc π).mpr hcov)
    · exact Or.inr (List.mem_map_of_mem hin)
  | dealloc hcond _ ih =>
    refine TraceOkFrom.dealloc ?_ ih
    rcases hcond with hcov | hin
    · exact Or.inl ((CapabilitySet.covers_renameLoc π).mpr hcov)
    · exact Or.inr (List.mem_map_of_mem hin)

/-- `TraceOk` is equivariant. -/
theorem TraceOk.renameLoc {C : CapabilitySet} {t : Trace} (h : TraceOk t C)
    (π : Equiv.Perm Nat) : TraceOk (t.renameLoc π) (C.renameLoc π) :=
  TraceOkFrom.renameLoc h π

/-- `Noninterference` is equivariant. -/
theorem CapabilitySet.Noninterference.renameLoc {C1 C2 : CapabilitySet}
    (h : CapabilitySet.Noninterference C1 C2) (π : Equiv.Perm Nat) :
    CapabilitySet.Noninterference (C1.renameLoc π) (C2.renameLoc π) := by
  induction h with
  | ni_symm _ ih => exact .ni_symm ih
  | ni_empty => exact .ni_empty
  | ni_union _ _ ih1 ih2 => exact .ni_union ih1 ih2
  | ni_ro => exact .ni_ro
  | ni_disj hne => exact .ni_disj (fun heq => hne (π.injective heq))

/-- `resolve` commutes with renaming. -/
theorem resolve_renameLoc (π : Equiv.Perm Nat) (h : Heap) (e : Exp {}) :
    resolve (h.renameLoc π) (e.renameLoc π) = (resolve h e).map (Exp.renameLoc π) := by
  cases e with
  | var x =>
    cases x with
    | bound b => cases b
    | free x0 =>
      simp only [Exp.renameLoc, Var.renameLoc, resolve, Heap.lookup_renameLoc]
      cases h x0 with
      | none => rfl
      | some c =>
        cases c with
        | val v => rfl
        | capability ci => rfl
        | masked => rfl
  | _ => rfl

/-- A single step is equivariant. -/
theorem Step.renameLoc {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hstep : Step t m e m' e') (π : Equiv.Perm Nat) :
    Step (t.renameLoc π) (m.renameLoc π) (e.renameLoc π)
      (m'.renameLoc π) (e'.renameLoc π) := by
  induction hstep with
  | step_apply hlk =>
    rw [Exp.openVar_renameLoc]
    exact Step.step_apply (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_invoke hlk1 hlk2 =>
    exact Step.step_invoke (by rw [Memory.lookup_renameLoc, hlk1]; rfl)
      (by rw [Memory.lookup_renameLoc, hlk2]; rfl)
  | step_tapply hlk =>
    rw [Exp.subst_renameLoc, Subst.openTVar_renameLoc]
    exact Step.step_tapply (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_capply hlk =>
    rw [Exp.subst_renameLoc, Subst.openCVar_renameLoc]
    exact Step.step_capply (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_unwrap hlk =>
    exact Step.step_unwrap (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_cond_var_true hlk =>
    exact Step.step_cond_var_true (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_cond_var_false hlk =>
    exact Step.step_cond_var_false (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_read hlk1 hlk2 =>
    simp only [Exp.renameLoc, apply_ite (Exp.renameLoc π)]
    exact Step.step_read (by rw [Memory.lookup_renameLoc, hlk1]; rfl)
      (by rw [Memory.lookup_renameLoc, hlk2]; rfl)
  | step_write_true hx hy =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    have hy' := Memory.lookup_val_renameLoc hy π
    rw [Memory.update_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact Step.step_write_true (hx := hx') hy'
  | step_write_false hx hy =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    have hy' := Memory.lookup_val_renameLoc hy π
    rw [Memory.update_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact Step.step_write_false (hx := hx') hy'
  | step_alloc hlk hfresh =>
    have hlk' := Memory.lookup_val_renameLoc hlk π
    simp only [HeapVal.renameLoc, apply_ite (Exp.renameLoc π), Exp.renameLoc] at hlk'
    rw [Memory.extend_mcell_renameLoc]
    exact Step.step_alloc hlk' (Memory.fresh_renameLoc hfresh π)
  | step_drop hx =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    rw [Memory.drop_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact Step.step_drop (hx := hx')
  | step_ctx_letin _ ih => exact Step.step_ctx_letin ih
  | step_ctx_unpack _ ih => exact Step.step_ctx_unpack ih
  | @step_par_left t m e1 m' e1' e2 C1 C2 _ ht hni ih =>
    simp only [Exp.renameLoc]
    rw [CaptureSet.growByAllocs_renameLoc]
    refine Step.step_par_left ih ?_ ?_
    · have := ht.renameLoc π
      rw [CaptureSet.reachability_renameLoc] at this
      exact this
    · have := hni.renameLoc π
      rw [CaptureSet.reachability_renameLoc, CaptureSet.reachability_renameLoc] at this
      exact this
  | @step_par_right t m C2 e2 m' e2' C1 e1 ht hni _ ih =>
    simp only [Exp.renameLoc]
    rw [CaptureSet.growByAllocs_renameLoc]
    refine Step.step_par_right ?_ ?_ ih
    · have := ht.renameLoc π
      rw [CaptureSet.reachability_renameLoc] at this
      exact this
    · have := hni.renameLoc π
      rw [CaptureSet.reachability_renameLoc, CaptureSet.reachability_renameLoc] at this
      exact this
  | step_par_join h1 h2 => exact Step.step_par_join (h1.renameLoc π) (h2.renameLoc π)
  | step_rename =>
    rw [Exp.openVar_renameLoc]; exact Step.step_rename
  | step_lift hvsimple hwf hfresh =>
    rw [Exp.openVar_renameLoc]
    rw [Memory.extend_compute_renameLoc (hwf' := hwf.renameLoc π)]
    exact Step.step_lift (hvsimple.renameLoc π) (hwf.renameLoc π)
      (Memory.fresh_renameLoc hfresh π)
  | step_unpack =>
    rw [Exp.subst_renameLoc, Subst.unpack_renameLoc]
    exact Step.step_unpack

/-- A multi-step reduction is equivariant. -/
theorem Reduce.renameLoc {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hred : Reduce t m e m' e') (π : Equiv.Perm Nat) :
    Reduce (t.renameLoc π) (m.renameLoc π) (e.renameLoc π)
      (m'.renameLoc π) (e'.renameLoc π) := by
  induction hred with
  | refl => exact Reduce.refl
  | step h _ ih =>
    rw [Trace.renameLoc_append]
    exact Reduce.step (h.renameLoc π) ih

/-- A single sequential step is equivariant. -/
theorem SeqStep.renameLoc {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hstep : SeqStep t m e m' e') (π : Equiv.Perm Nat) :
    SeqStep (t.renameLoc π) (m.renameLoc π) (e.renameLoc π)
      (m'.renameLoc π) (e'.renameLoc π) := by
  induction hstep with
  | step_apply hlk =>
    rw [Exp.openVar_renameLoc]
    exact SeqStep.step_apply (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_invoke hlk1 hlk2 =>
    exact SeqStep.step_invoke (by rw [Memory.lookup_renameLoc, hlk1]; rfl)
      (by rw [Memory.lookup_renameLoc, hlk2]; rfl)
  | step_tapply hlk =>
    rw [Exp.subst_renameLoc, Subst.openTVar_renameLoc]
    exact SeqStep.step_tapply (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_capply hlk =>
    rw [Exp.subst_renameLoc, Subst.openCVar_renameLoc]
    exact SeqStep.step_capply (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_unwrap hlk =>
    exact SeqStep.step_unwrap (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_cond_var_true hlk =>
    exact SeqStep.step_cond_var_true (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_cond_var_false hlk =>
    exact SeqStep.step_cond_var_false (by rw [Memory.lookup_renameLoc, hlk]; rfl)
  | step_read hlk1 hlk2 =>
    simp only [Exp.renameLoc, apply_ite (Exp.renameLoc π)]
    exact SeqStep.step_read (by rw [Memory.lookup_renameLoc, hlk1]; rfl)
      (by rw [Memory.lookup_renameLoc, hlk2]; rfl)
  | step_write_true hx hy =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    have hy' := Memory.lookup_val_renameLoc hy π
    rw [Memory.update_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact SeqStep.step_write_true (hx := hx') hy'
  | step_write_false hx hy =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    have hy' := Memory.lookup_val_renameLoc hy π
    rw [Memory.update_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact SeqStep.step_write_false (hx := hx') hy'
  | step_alloc hlk hfresh =>
    have hlk' := Memory.lookup_val_renameLoc hlk π
    simp only [HeapVal.renameLoc, apply_ite (Exp.renameLoc π), Exp.renameLoc] at hlk'
    rw [Memory.extend_mcell_renameLoc]
    exact SeqStep.step_alloc hlk' (Memory.fresh_renameLoc hfresh π)
  | step_drop hx =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    rw [Memory.drop_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact SeqStep.step_drop (hx := hx')
  | step_ctx_letin _ ih => exact SeqStep.step_ctx_letin ih
  | step_ctx_unpack _ ih => exact SeqStep.step_ctx_unpack ih
  | step_par_left _ ih =>
    simp only [Exp.renameLoc]
    rw [CaptureSet.growByAllocs_renameLoc]
    exact SeqStep.step_par_left ih
  | step_par_right hans _ ih =>
    simp only [Exp.renameLoc]
    rw [CaptureSet.growByAllocs_renameLoc]
    exact SeqStep.step_par_right (hans.renameLoc π) ih
  | step_par_join h1 h2 => exact SeqStep.step_par_join (h1.renameLoc π) (h2.renameLoc π)
  | step_rename =>
    rw [Exp.openVar_renameLoc]; exact SeqStep.step_rename
  | step_lift hvsimple hwf hfresh =>
    rw [Exp.openVar_renameLoc]
    rw [Memory.extend_compute_renameLoc (hwf' := hwf.renameLoc π)]
    exact SeqStep.step_lift (hvsimple.renameLoc π) (hwf.renameLoc π)
      (Memory.fresh_renameLoc hfresh π)
  | step_unpack =>
    rw [Exp.subst_renameLoc, Subst.unpack_renameLoc]
    exact SeqStep.step_unpack

/-- A multi-step sequential reduction is equivariant. -/
theorem SeqReduce.renameLoc {t : Trace} {m m' : Memory} {e e' : Exp {}}
    (hred : SeqReduce t m e m' e') (π : Equiv.Perm Nat) :
    SeqReduce (t.renameLoc π) (m.renameLoc π) (e.renameLoc π)
      (m'.renameLoc π) (e'.renameLoc π) := by
  induction hred with
  | refl => exact SeqReduce.refl
  | step h _ ih =>
    rw [Trace.renameLoc_append]
    exact SeqReduce.step (h.renameLoc π) ih

/-- A big-step evaluation is equivariant. -/
theorem BigStep.renameLoc {t : Trace} {m m' : Memory} {e v : Exp {}}
    (hbs : BigStep m e t v m') (π : Equiv.Perm Nat) :
    BigStep (m.renameLoc π) (e.renameLoc π) (t.renameLoc π)
      (v.renameLoc π) (m'.renameLoc π) := by
  induction hbs with
  | bs_pack => exact BigStep.bs_pack
  | bs_alloc hlk hfresh =>
    have hlk' := Memory.lookup_val_renameLoc hlk π
    simp only [HeapVal.renameLoc, apply_ite (Exp.renameLoc π), Exp.renameLoc] at hlk'
    rw [Memory.extend_mcell_renameLoc]
    exact BigStep.bs_alloc hlk' (Memory.fresh_renameLoc hfresh π)
  | bs_val hv => exact BigStep.bs_val (hv.renameLoc π)
  | bs_var => exact BigStep.bs_var
  | bs_apply hlk _ ih =>
    rw [Exp.subst_renameLoc, Subst.openVar_var_renameLoc] at ih
    exact BigStep.bs_apply (by rw [Memory.lookup_renameLoc, hlk]; rfl) ih
  | bs_invoke hlk1 hlk2 =>
    exact BigStep.bs_invoke (by rw [Memory.lookup_renameLoc, hlk1]; rfl)
      (by rw [Memory.lookup_renameLoc, hlk2]; rfl)
  | bs_tapply hlk _ ih =>
    rw [Exp.subst_renameLoc, Subst.openTVar_renameLoc] at ih
    exact BigStep.bs_tapply (by rw [Memory.lookup_renameLoc, hlk]; rfl) ih
  | bs_capply hlk _ ih =>
    rw [Exp.subst_renameLoc, Subst.openCVar_renameLoc] at ih
    exact BigStep.bs_capply (by rw [Memory.lookup_renameLoc, hlk]; rfl) ih
  | bs_wrap => exact BigStep.bs_wrap
  | bs_unwrap hlk _ ih =>
    exact BigStep.bs_unwrap (by rw [Memory.lookup_renameLoc, hlk]; rfl) ih
  | bs_letin_val hbs1 hvsimple hwf hfresh _ ih1 ih2 =>
    rw [Trace.renameLoc_append]
    refine BigStep.bs_letin_val ih1 (hvsimple.renameLoc π) (hwf.renameLoc π)
      (Memory.fresh_renameLoc hfresh π) ?_
    rw [Exp.openVar_renameLoc] at ih2
    rwa [Memory.extend_val_compute_renameLoc (hwf' := hwf.renameLoc π)] at ih2
  | bs_letin_var hbs1 _ ih1 ih2 =>
    rw [Trace.renameLoc_append]
    rw [Exp.subst_renameLoc, Subst.openVar_var_renameLoc] at ih2
    exact BigStep.bs_letin_var ih1 ih2
  | bs_unpack hbs1 _ ih1 ih2 =>
    rw [Trace.renameLoc_append]
    rw [Exp.subst_renameLoc, Subst.unpack_renameLoc] at ih2
    exact BigStep.bs_unpack ih1 ih2
  | bs_read hlk1 hlk2 =>
    simp only [Exp.renameLoc, apply_ite (Exp.renameLoc π)]
    exact BigStep.bs_read (by rw [Memory.lookup_renameLoc, hlk1]; rfl)
      (by rw [Memory.lookup_renameLoc, hlk2]; rfl)
  | bs_write_true hx hy =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    have hy' := Memory.lookup_val_renameLoc hy π
    rw [Memory.update_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact BigStep.bs_write_true (hx := hx') hy'
  | bs_write_false hx hy =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    have hy' := Memory.lookup_val_renameLoc hy π
    rw [Memory.update_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact BigStep.bs_write_false (hx := hx') hy'
  | bs_drop hx =>
    have hx' := Memory.lookup_cap_renameLoc hx π
    rw [Memory.drop_mcell_renameLoc (hexists' := ⟨_, hx'⟩)]
    exact BigStep.bs_drop (hx := hx')
  | bs_cond_true hres _ ih =>
    refine BigStep.bs_cond_true ?_ ih
    rename_i mm xx _
    have key := resolve_renameLoc π mm.heap (.var xx)
    rw [hres] at key
    exact key
  | bs_cond_false hres _ ih =>
    refine BigStep.bs_cond_false ?_ ih
    rename_i mm xx _
    have key := resolve_renameLoc π mm.heap (.var xx)
    rw [hres] at key
    exact key
  | bs_par _ _ ih1 ih2 =>
    rw [Trace.renameLoc_append]
    exact BigStep.bs_par ih1 ih2

end CoreCapybara
