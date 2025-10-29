# CC Refactoring: Explicit Captures

**Status**: Core + Denotation + Soundness (Partial) Complete
**Date**: 2025-10-29 (Updated)

## Motivation

Original design used `HeapTopology : Nat -> CapabilitySet` to track reachability, causing circularity: type denotations need topology, but topology construction needs type information.

**Solution**: Make captures explicit in abstractions (`λ[cs]x.e`). Eagerly compute and store transitive capability closure at allocation time.

## Core Design Changes

### 1. Syntax Changes (✅ Complete)

**Before**:
```lean
| abs : Ty .capt s -> Exp (s,x) -> Exp s
| tabs : Ty .shape s -> Exp (s,X) -> Exp s
| cabs : CaptureBound s -> Exp (s,C) -> Exp s
```

**After**:
```lean
| abs : CaptureSet s -> Ty .capt s -> Exp (s,x) -> Exp s
| tabs : CaptureSet s -> Ty .shape s -> Exp (s,X) -> Exp s
| cabs : CaptureSet s -> CaptureBound s -> Exp (s,C) -> Exp s
```

Abstractions now carry explicit capture sets indicating what they capture.

### 2. Heap Values (✅ Complete)

```lean
structure HeapVal where
  unwrap : Exp {}              -- closed expressions only
  isVal : unwrap.IsSimpleVal   -- abs, tabs, cabs, unit (excludes pack)
  reachability : CapabilitySet -- precomputed transitive closure
```

### 3. Reachability Computation (✅ Complete)

```lean
def reachability_of_loc (h : Heap) (l : Nat) : CapabilitySet
def expand_captures (h : Heap) (cs : CaptureSet {}) : CapabilitySet
def compute_reachability (h : Heap) (v : Exp {}) (hv : v.IsSimpleVal) : CapabilitySet
```

**Transitive closure**: For `λ[{f}]x.e`, if `f` captures `{c}`, then `expand_captures h {f} = {c}`. Computed at allocation time in `eval_letin`.

### 4. Monotonicity Theorems (✅ Proven)

```lean
theorem reachability_of_loc_monotonic : h2.subsumes h1 → reachability_of_loc h2 l = reachability_of_loc h1 l
theorem expand_captures_monotonic : h2.subsumes h1 → expand_captures h2 cs = expand_captures h1 cs
theorem compute_reachability_monotonic : h2.subsumes h1 → compute_reachability h2 v hv = compute_reachability h1 v hv
```

**Significance**: Reachability is stable under heap growth.

### 5. HeapTopology Elimination (✅ Complete)

Removed `HeapTopology` entirely. With explicit captures, topology is redundant:
- Denotations: `TypeEnv s -> T -> Denot` (no `HeapTopology` parameter)
- EnvTyping: `Ctx s -> TypeEnv s -> Memory -> Prop`
- Notation: `⟦T⟧_[ρ]` (was `⟦T⟧_[ρ,φ]`)

### 6. Well-Formedness (✅ Complete)

```lean
Ty.capt_val_denot ρ (.capt C S) mem exp =
  exp.WfInHeap mem.heap ∧ Ty.shape_val_denot ρ S (C.denot ρ) mem exp
```

**Impact**: Well-formedness of `(.var (.free n))` guarantees `n` exists in heap, enabling `reachability_of_loc_monotonic`.

## Files Status

### ✅ Completed

**Core Infrastructure:**
- `Semantic/CC/Syntax/Exp.lean` - Added `CaptureSet` to abs/tabs/cabs
- `Semantic/CC/Substitution.lean` - Updated `Exp.subst` to handle capture sets
- `Semantic/CC/Eval/Heap.lean` - Changed `Val {}` to `HeapVal` with reachability
- `Semantic/CC/Eval/BigStep.lean` - Reachability functions + monotonicity theorems
- `Semantic/Prelude.lean` - Simplified notation (removed `HeapTopology` parameter)

**Denotational Semantics:**
- `Semantic/CC/Denotation/Core.lean` - All denotations updated, `HeapTopology` removed
- `Semantic/CC/Denotation/Rebind.lean` - All rebinding theorems fixed, weakening lemmas restored
- `Semantic/CC/Denotation/Retype.lean` - All retyping theorems fixed, `open_*` lemmas complete

**Soundness (Partial):**
- `Semantic/CC/Soundness.lean` - Abstraction theorems compile with documented gaps:
  - `sem_typ_abs`, `sem_typ_tabs`, `sem_typ_cabs` - Fixed for explicit captures
  - `abs_val_denot_inv` - Updated for HeapVal structure
  - `sem_typ_app` - Compiles with identified proof obligations

### 📝 Remaining Work

**Critical Missing Lemmas:**
1. `reachability_of_loc H' arg = T1.captureSet.denot env` - Relate heap reachability to type capture sets
2. `open_arg_exi_exp_denot` - Opening lemma for existential types
3. Capability set relationships from typing judgments
4. Eval monotonicity wrt capability sets

**Files:**
- `TypeSystem.lean` - Update typing rules for explicit captures
- `Soundness.lean` - Complete remaining proofs (sem_typ_tapp, sem_typ_letin, subtyping)

## Key Implementation Patterns

**Abstraction witnesses** - All abstractions now provide 3 components:
```lean
obtain ⟨cs, T0, t0, hr, hd⟩ := h  -- capture set, type, body
use cs, T0, t0
```

**Reachability parameter** - Environment extensions require explicit reachability:
```lean
ρ.liftVar (x:=arg) (R:=reachability_of_loc H' arg)
```

**Cpoly quantification** - Quantify over syntactic capture sets, compute semantic value:
```lean
intro H' CS hsub hsub_bound
let A0 := CS.denot TypeEnv.empty
```

**Well-formedness** - `capt_val_denot` now includes `WfInHeap` conjunction:
```lean
exp.WfInHeap mem.heap ∧ Ty.shape_val_denot ρ S (C.denot ρ) mem exp
```
