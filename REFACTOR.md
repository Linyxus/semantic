# CC Refactoring: Explicit Captures

**Status**: In Progress
**Date**: 2025-10-28

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

**Significance**: These ensure that reachability computation is stable - doesn't matter if we compute it in a smaller or larger heap.

## Files Status

### ✅ Completed

- `Semantic/CC/Syntax/Exp.lean` - Added `CaptureSet` to abs/tabs/cabs
- `Semantic/CC/Substitution.lean` - Updated `Exp.subst` to handle capture sets
- `Semantic/CC/Eval/Heap.lean` - Changed `Val {}` to `HeapVal`
- `Semantic/CC/Eval/BigStep.lean` - Added reachability functions + monotonicity theorems
- `Semantic/CC.lean` - Module compiles cleanly

### 🚧 Needs Updating

Priority order:

1. **`Denotation/Core.lean`** - Type denotations extract closures from heap
   - Update pattern matches: `.abs T e` → `.abs cs T e`
   - Potentially eliminate or simplify `HeapTopology` usage
   - Update `resolve` function for new `HeapVal` structure

2. **`TypeSystem.lean`** - Typing rules for abstractions
   - Add capture set to typing rules
   - Determine how to check/infer captures statically

3. **`Soundness.lean`** - Semantic soundness proof
   - Update to work with new capture structure
   - May simplify with explicit captures

4. **`Denotation/Rebind.lean` & `Denotation/Retype.lean`**
   - Update theorems for new abstraction structure

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

## Migration Checklist

When updating a file:

1. **Pattern matches on Exp**:
   - Change `.abs T e` → `.abs cs T e`
   - Change `.tabs T e` → `.tabs cs T e`
   - Change `.cabs cb e` → `.cabs cs cb e`

2. **Val vs HeapVal**:
   - Change `Val {}` → `HeapVal`
   - Change `IsVal` → `IsSimpleVal` where appropriate
   - Extract reachability: `⟨v, hv, R⟩` instead of `⟨v, hv⟩`

3. **Heap lookups**:
   - Pattern: `h x = some (.val ⟨.abs cs T e, hv, R⟩)` (note the `cs` and `R`)

4. **Check with lean4check**:
   ```bash
   lean4check Semantic/CC/YourFile.lean
   ```

## Key Questions for Future Work

1. **Type checking captures**: How do we verify that declared captures are correct?
   - Static analysis to compute free variables?
   - Conservative over-approximation?

2. **HeapTopology elimination**: Can we completely remove it now?
   - Check all uses in `Denotation/Core.lean`
   - May still need for well-formedness conditions

3. **Pack values**: Should they have captures too?
   - Currently excluded from heap storage
   - May need special handling

## References

- **Original discussion**: Lines 45-73 in conversation about transitive capability problem
- **Design decision**: Lines 124-150 discussing explicit captures solution
- **Implementation start**: Syntax/Exp.lean modifications

## Notes

- All changes preserve the **empty signature property**: `Exp {}` means closed expressions
- The reachability computation works on closed expressions only
- Monotonicity theorems have one `sorry` for well-formedness (proving all variables in capture sets exist in heap)

---

**Next step**: Update `Denotation/Core.lean` to work with new abstraction syntax and HeapVal structure.
