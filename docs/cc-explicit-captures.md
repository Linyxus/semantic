# CC Refactoring: Explicit Captures

**Status**: Core + Denotation Complete
**Date**: 2025-10-29 (Updated)

## Motivation

The original design used `HeapTopology : Nat -> CapabilitySet` to track capability reachability. This created fundamental issues:

1. **Circularity**: Type denotations need heap topology, but topology construction needs type information
2. **Non-constructive**: Topology appeared "magically" without clear construction
3. **Variable problem**: When `{x}` appears in a capture set and `x` points to a value (not capability), we need to know what capabilities that value transitively uses - but we don't have this information when interpreting types

**Solution**: Make captures explicit in abstraction syntax. When creating a closure, eagerly compute and store its transitive capability closure.

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

**Before**:
```lean
structure Val (s : Sig) where
  unwrap : Exp s
  isVal : unwrap.IsVal
```

**After**:
```lean
structure HeapVal where
  unwrap : Exp {}
  isVal : unwrap.IsSimpleVal  -- Note: IsSimpleVal excludes pack
  reachability : CapabilitySet
```

Key changes:
- Values are closed (`Exp {}`)
- Use `IsSimpleVal` (excludes `pack`, includes only `abs`, `tabs`, `cabs`, `unit`)
- Carry precomputed `reachability` - the transitive capability closure

### 3. Reachability Computation (✅ Complete)

Three new functions in `Eval/BigStep.lean`:

```lean
-- Extract reachability from a heap location
def reachability_of_loc (h : Heap) (l : Nat) : CapabilitySet

-- Expand a capture set to actual capabilities by resolving variables
def expand_captures (h : Heap) (cs : CaptureSet {}) : CapabilitySet

-- Compute transitive reachability for a value
def compute_reachability (h : Heap) (v : Exp {}) (hv : v.IsSimpleVal) : CapabilitySet
```

**How it works**:
- When creating abstraction `λ[cs]x.e`, the capture set `cs` contains variables like `{f, g}`
- `expand_captures h cs` resolves each variable by looking up its reachability in the heap
- For `cs = {f}`, if `h(f) = ⟨λ[{c}]y.e', _, {c}⟩`, then `expand_captures h {f} = {c}`
- This gives us transitive closure: if `g` captures `f` which captures `c`, then `{g}` expands to `{c}`

### 4. Key Theorems (✅ Proven)

Three monotonicity theorems ensure reachability is well-behaved under heap growth:

```lean
theorem reachability_of_loc_monotonic
  (hsub : h2.subsumes h1) (hex : h1 l = some v) :
  reachability_of_loc h2 l = reachability_of_loc h1 l

theorem expand_captures_monotonic
  (hsub : h2.subsumes h1) (cs : CaptureSet {}) :
  expand_captures h2 cs = expand_captures h1 cs

theorem compute_reachability_monotonic
  (hsub : h2.subsumes h1) (v : Exp {}) (hv : v.IsSimpleVal) :
  compute_reachability h2 v hv = compute_reachability h1 v hv
```

**Significance**: These ensure reachability computation is stable - doesn't matter if we compute it in a smaller or larger heap.

### 5. HeapTopology Elimination (✅ Complete)

**HeapTopology is completely removed from the codebase.**

Key insight: With explicit captures, the topology became redundant because:
- `HeapVal` stores precomputed `reachability`
- `reachability_of_loc : Memory -> Nat -> CapabilitySet` extracts it on-demand
- `CaptureSet.denot` never actually used the topology meaningfully

**Changes made**:
1. Removed `HeapTopology` type and `HeapTopology.extend`
2. Updated all denotation signatures: `TypeEnv s -> T -> Denot` (no `HeapTopology` parameter)
3. Simplified `EnvTyping`: `Ctx s -> TypeEnv s -> Memory -> Prop`
4. Updated notation in `Prelude.lean`: `⟦T⟧_[ρ]` instead of `⟦T⟧_[ρ,φ]`

### 6. Well-Formedness Requirement (✅ Complete)

Added well-formedness to `capt_val_denot`:
```lean
def Ty.capt_val_denot : TypeEnv s -> Ty .capt s -> Denot
| ρ, .capt C S => fun mem exp =>
  exp.WfInHeap mem.heap ∧
  Ty.shape_val_denot ρ S (C.denot ρ) mem exp
```

**Impact**: This solved the `env_typing_monotonic` proof! Well-formedness of `(.var (.free n))` implies `n` exists in the heap, which is exactly what `reachability_of_loc_monotonic` needs.

## Files Status

### ✅ Completed

**Core Infrastructure:**
- `Semantic/CC/Syntax/Exp.lean` - Added `CaptureSet` to abs/tabs/cabs
- `Semantic/CC/Substitution.lean` - Updated `Exp.subst` to handle capture sets
- `Semantic/CC/Eval/Heap.lean` - Changed `Val {}` to `HeapVal` with reachability
- `Semantic/CC/Eval/BigStep.lean` - Reachability functions + monotonicity theorems
- `Semantic/Prelude.lean` - Simplified notation (removed `HeapTopology` parameter)

**Denotational Semantics:**
- **`Semantic/CC/Denotation/Core.lean`** - All denotations updated, `HeapTopology` removed
- **`Semantic/CC/Denotation/Rebind.lean`** - All rebinding theorems fixed, weakening lemmas restored
- **`Semantic/CC/Denotation/Retype.lean`** - All retyping theorems fixed, `open_*` lemmas complete

### 📝 Remaining Work

1. **`TypeSystem.lean`** - Update typing rules for explicit captures
2. **`Soundness.lean`** - Fix semantic soundness proof (5 `sorry`s remaining)

## Design Philosophy

### Explicit vs Implicit Captures

**Explicit captures** (current approach):
- ✅ Constructive - reachability is computed, not assumed
- ✅ Local - stored with the value, not in external topology
- ✅ Self-describing - closures carry their own reachability
- ⚠️ Requires typing rules to verify captures are correct

**Key invariant**: For `λ[cs]x.e`, the capture set `cs` must include all free locations used by `e`.

### Heap Values vs General Values

We distinguish:
- **Simple values** (`IsSimpleVal`): abs, tabs, cabs, unit - can be stored in heap
- **Pack values** (`pack cs x`): Cannot be stored directly in heap

This simplifies heap structure - packs must be unpacked before heap allocation.

### Evaluation Strategy

In `eval_letin`, when allocating a value:
```lean
h1.extend l' ⟨v, hv, compute_reachability h1 v hv⟩
```

We compute reachability **at allocation time** using the current heap state. The monotonicity theorems ensure this is well-defined.

## Key Implementation Notes

### Syntax Changes
```lean
-- Expressions now have explicit capture sets
| .abs cs T e    -- λ[cs](x:T).e
| .tabs cs S e   -- Λ[cs](X<:S).e
| .cabs cs B e   -- Λ[cs](C<:B).e

-- HeapVal structure
⟨v, hv, R⟩ where R : CapabilitySet  -- precomputed reachability

-- Denotation signatures (no HeapTopology!)
Ty.shape_val_denot : TypeEnv s -> Ty .shape s -> PreDenot
CaptureSet.denot : TypeEnv s -> CaptureSet s -> CapabilitySet
```

### Critical Fixes Applied

**Arrow/Poly/Cpoly denotations:** Abstractions now have 3 witnesses (cs, T0, t0):
```lean
obtain ⟨cs, T0, t0, hr, hd⟩ := h
use cs, T0, t0
```

**Reachability in liftVar:** Must provide same reachability on both sides:
```lean
ρ.liftVar (x:=arg) (R:=reachability_of_loc H' arg)
```

**Well-formedness in capt_val_denot:** Introduce hypothesis, then prove shape equivalence:
```lean
intro hwf
exact hS (C.denot env1) s e
```

**Cpoly quantification:** Use `CS : CaptureSet {}` with `let A0 := CS.denot TypeEnv.empty`:
```lean
intro H' CS hsub hsub_bound
let A0 := CS.denot TypeEnv.empty
have ih2 := retype_exi_exp_denot (ρ.liftCVar (c:=A0)) T
```

**Open functions:** Destructure `interp_var` for `extend_var`:
```lean
env.extend_var (interp_var env y).1 (interp_var env y).2
```

## Next Steps

1. **TypeSystem.lean**: Add typing rules to verify declared captures are correct
2. **Soundness.lean**: Complete semantic type soundness proof
   - Need lemma: `open_arg_exi_exp_denot`
   - Need: Capability set relationships from typing
   - Need: Eval monotonicity wrt capability sets
