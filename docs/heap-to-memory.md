# Heap to Memory Refactor

## Overview

This refactor replaces raw `Heap` with well-formed `Memory` throughout the denotational semantics in `Semantic.CC`, enforcing well-formedness invariants at the type level.

## Motivation

**Before:** Well-formedness was a separate proposition that had to be manually threaded through proofs.

**After:** Well-formedness is enforced by the type system via the `Memory` structure:

```lean
structure Memory where
  heap : Heap
  wf : heap.WfHeap
```

This is a classic **type-driven design** improvement: semantic invariants that were previously manual proof obligations are now impossible to violate.

## Key Changes

### 1. Core Definitions (Denotation/Core.lean)

**Denot**: `Heap -> Exp {} -> Prop` → `Memory -> Exp {} -> Prop`

All denotation operations now work with `Memory`:
- `shape_val_denot`, `capt_val_denot`, `exi_val_denot` (value denotations)
- `capt_exp_denot`, `exi_exp_denot` (expression denotations)
- `EnvTyping` (typing contexts)
- `SemanticTyping` (semantic typing judgment)

### 2. Properties and Relations

**Monotonicity:**
- Old: `∀ {h1 h2}, h2.subsumes h1 -> ...`
- New: `∀ {m1 m2}, m2.subsumes m1 -> ...`

**Transparency:**
- Old: Uses direct heap lookup `h x = some (.val v)`
- New: Uses memory lookup `m.lookup x = some (.val v)`

**Mpost.is_monotonic:**
```lean
-- Now requires well-formedness as first argument
def Mpost.is_monotonic (Q : Mpost) : Prop :=
  ∀ {m1 m2 : Memory} {e},
    (hwf_e : e.WfInHeap m1.heap) ->
    m2.subsumes m1 ->
    Q e m1 ->
    Q e m2
```

### 3. Evaluation (BigStep.lean)

**Eval relation:** Already used `Memory`, updated to match new `Mpost.is_monotonic`.

**eval_monotonic theorem:** Updated to pass well-formedness to monotonicity proofs:
```lean
apply hpred hwf hsub hQ  -- was: apply hpred hsub hQ
```

### 4. Removed Temporaries

- **`Heap.to_memory`**: Temporary helper with `sorry` - removed
- **`Denot.as_post`**: Converted `Denot` to `Hpost` - removed (only `as_mpost` remains)

## Status

✅ **Complete** - All files compile successfully.

The refactor successfully moves from implicit well-formedness (manual tracking) to explicit well-formedness (type-enforced), making the denotational semantics more robust and easier to maintain.

## Implementation Details

### Well-formedness Threading

Expression denotations now explicitly require well-formedness (user addition):
```lean
def Ty.capt_exp_denot : TypeEnv s -> HeapTopology -> Ty .capt s -> PreDenot
| ρ, φ, T => fun A m (e : Exp {}) =>
  (hwf_e : e.WfInHeap m.heap) ->
  Eval A m e (Ty.capt_val_denot ρ φ T).as_mpost
```

### Monotonicity Lemmas

Expression monotonicity now requires explicit well-formedness assumptions:
```lean
def capt_exp_denot_is_monotonic :
  ∀ {C : CapabilitySet} {m1 m2 : Memory} {e : Exp {}},
    Exp.WfInHeap e m1.heap ->  -- Explicit assumption
    m2.subsumes m1 ->
    (Ty.capt_exp_denot env φ T) C m1 e ->
    (Ty.capt_exp_denot env φ T) C m2 e
```

This is justified because semantic typing only considers well-typed expressions, which are well-formed when substituted with typed environments.
