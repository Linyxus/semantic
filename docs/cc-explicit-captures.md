# CC Refactoring: Explicit Captures

**Status**: Core Complete, Proofs In Progress
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

- `Semantic/CC/Syntax/Exp.lean` - Added `CaptureSet` to abs/tabs/cabs
- `Semantic/CC/Substitution.lean` - Updated `Exp.subst` to handle capture sets
- `Semantic/CC/Eval/Heap.lean` - Changed `Val {}` to `HeapVal` with reachability
- `Semantic/CC/Eval/BigStep.lean` - Reachability functions + monotonicity theorems
- `Semantic/Prelude.lean` - Simplified notation (removed `HeapTopology` parameter)
- **`Semantic/CC/Denotation/Core.lean`** - All denotations updated, `HeapTopology` removed, all proofs compile

### 🚧 In Progress

1. **`Denotation/Rebind.lean`** - Updating rebinding theorems
   - Mutual theorems (`rebind_*_denot`) signatures updated, need fixing arrow/poly cases
   - Weakening lemmas commented out temporarily

### 📝 Not Started

1. **`Denotation/Retype.lean`** - Similar updates needed as Rebind.lean
2. **`TypeSystem.lean`** - Typing rules for abstractions with capture sets
3. **`Soundness.lean`** - Semantic soundness proof updates

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

## Key Implementation Notes for Future Claude Sessions

### Pattern Matching After Refactoring
```lean
-- Expressions now have capture sets
| .abs cs T e    -- λ[cs](x:T).e
| .tabs cs S e   -- Λ[cs](X<:S).e
| .cabs cs B e   -- Λ[cs](C<:B).e

-- HeapVal structure
⟨v, hv, R⟩ where R : CapabilitySet  -- precomputed reachability

-- Denotation signatures (no HeapTopology!)
Ty.shape_val_denot : TypeEnv s -> Ty .shape s -> PreDenot
CaptureSet.denot : TypeEnv s -> CaptureSet s -> CapabilitySet
```

### Common Patterns in Rebind.lean

**Problem**: Recursive calls in arrow/poly cases refer to old signatures with `φ`.

**Solution Pattern**:
```lean
-- OLD (broken):
have ih2 := rebind_exi_exp_denot (φ:=φ.extend arg _) (ρ.liftVar) T2

-- NEW (correct):
have ih2 := rebind_exi_exp_denot (ρ.liftVar (x:=arg)) T2
```

**Key insight**: Removing `φ` means removing ALL references to it, including:
- Named arguments `(φ:=...)`
- `φ.extend` calls - these are now meaningless
- The mutual theorems work the same, just simpler signatures

### Debugging with lean4check

```bash
# Use the MCP tool - it gives better error messages
mcp__lean4check__check Semantic/CC/Denotation/Rebind.lean

# For incremental compilation during fixes
lake build Semantic.CC.Denotation.Rebind 2>&1 | grep -A 5 "error:"
```

### Common Errors After HeapTopology Removal

1. **"Invalid argument name `φ`"** - Remove all `(φ:=...)` named arguments
2. **"Application type mismatch" expecting HeapTopology** - Remove the `φ` parameter completely
3. **Obtain pattern has wrong number of fields** - Check if extracting from old 4-tuple, now 3-tuple (removed cs field in some places)

## Open Questions

1. **Type checking captures**: How to statically verify declared captures are correct?
2. **Pack values**: Should they carry captures? Currently excluded from heap storage.
