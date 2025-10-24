# CC Soundness Porting Status

**Last Updated**: 2025-10-24
**File**: `Semantic/CC/Soundness.lean`
**Task**: Port type soundness proofs from Fsub to CC (Capture Calculus)

## Overview

We are porting type soundness proofs from `Semantic/Fsub/Soundness.lean` to `Semantic/CC/Soundness.lean`. The CC codebase implements Capture Calculus with significant architectural differences from Fsub that require careful adaptation of all proofs.

## Key Architectural Differences: Fsub vs CC

### 1. Three-Sorted Type System
- **Fsub**: Single type sort
- **CC**: Three sorts with different semantics:
  - `.shape` types: Return `PreDenot = CapabilitySet -> Denot`
  - `.capt` types: Capturing types (shape + capture set)
  - `.exi` types: Existential types (used for expression results)

### 2. Type Denotations
```lean
-- Fsub (WRONG for CC):
Ty.val_denot : TypeEnv s -> Ty s -> Denot
Ty.exp_denot : TypeEnv s -> Ty s -> Denot

-- CC (CORRECT):
Ty.shape_val_denot : TypeEnv s -> Ty .shape s -> PreDenot
Ty.capt_val_denot  : TypeEnv s -> Ty .capt s -> Denot
Ty.exi_val_denot   : TypeEnv s -> Ty .exi s -> Denot
Ty.exi_exp_denot   : TypeEnv s -> Ty .exi s -> Denot
-- (also capt_exp_denot, but less commonly used)
```

### 3. Type Constructors
```lean
-- Arrow type:
.arrow : Ty .capt s -> Ty .exi (s,x) -> Ty .shape s

-- Poly type:
.poly : Ty .shape s -> Ty .exi (s,X) -> Ty .shape s

-- Capturing type wrapper:
.capt : CaptureSet s -> Ty .shape s -> Ty .capt s

-- Existential type wrappers:
.typ : Ty .capt s -> Ty .exi s        -- for values
.exi : Ty .capt (s,C) -> Ty .exi s    -- for existential quantification
```

### 4. Capture Sets
- **Fsub**: No capture tracking
- **CC**: Every semantic typing judgment includes a capture set parameter
```lean
-- Fsub notation:
Γ ⊨ e : T

-- CC notation:
C # Γ ⊨ e : T    -- where C : CaptureSet s
```

### 5. Variable Interpretation
```lean
-- Fsub:
TypeEnv.lookup_var : TypeEnv s -> BVar s .var -> Nat

-- CC:
TypeEnv.lookup_var : TypeEnv s -> BVar s .var -> Nat × CapabilitySet
-- Must extract .1 to get the Nat
```

### 6. Three Variable Kinds
- `.var`: Term variables (x)
- `.tvar`: Type variables (X)
- `.cvar`: Capture variables (C) - **NEW in CC**

All proofs that traverse environments must handle the `.cvar` case.

### 7. Environment Extension
```lean
-- Variable extension requires both index and capability set:
TypeEnv.extend_var : TypeEnv s -> Nat -> CapabilitySet -> TypeEnv (s,x)

-- In arrow denotation:
env.extend_var arg (T1.captureSet.denot env)
```

## Completed Work

### ✅ typed_env_lookup_var (lines 5-63)
**Status**: Fully ported and compiles

**Key changes made**:
1. Changed return type from generic `Ty.val_denot` to `Ty.capt_val_denot`
2. Extract `.1` from `(env.lookup_var x).1` to get Nat index
3. Handle all three binding cases:
   - `.var`: Use `weaken_capt_val_denot` with parameter `A` (not `access`)
   - `.tvar`: Use `tweaken_capt_val_denot`
   - `.cvar`: Use `cweaken_capt_val_denot` (NEW)

**Critical fix**: Parameter name is `A` not `access`:
```lean
-- WRONG:
weaken_capt_val_denot (env:=env0) (x:=n) (access:=access) (T:=T0)

-- CORRECT:
weaken_capt_val_denot (env:=env0) (x:=n) (A:=access) (T:=T0)
```

### ✅ sem_typ_var (lines 65-72)
**Status**: Fully ported and compiles

**Key changes made**:
1. Added capture set to semantic typing: `T.captureSet # Γ ⊨ (.var (.bound x)) : (.typ T)`
2. Use `Ty.exi_exp_denot` and `Ty.exi_val_denot` instead of generic versions
3. Wrap type in `.typ` constructor for existential type

## In Progress: sem_typ_abs (lines 74-91)

### Current Status
**Signature**: ✅ Fixed and compiles
```lean
theorem sem_typ_abs
  (ht : Cbody # (Γ,x:T1) ⊨ e : T2) :
  Cfun # Γ ⊨ (.abs T1 e) : (.typ (.capt Cfun (.arrow T1 T2))) := by
```

**Proof body**: ❌ Has type errors

### Issues to Fix

1. **Missing lemma** (line 86):
```lean
simp [Exp.from_TypeEnv_weaken_open]  -- ERROR: Unknown constant
```
This lemma is commented out in `CC/Denotation/Core.lean:283-287`. Two options:
- Uncomment and prove the lemma
- Rewrite proof without using it (may need manual term construction)

2. **Type mismatch in `use` tactic** (line 82):
```lean
use T1, e
-- Error: T1 has type Ty .capt s but expected Ty .capt []
-- Error: e has type Exp (s,x) but expected Exp ([],x)
```
This suggests the goal context has wrong signature. The issue is that after `intro env store hts`, we're in a context where types are instantiated to the empty signature.

**Analysis**: The arrow denotation from `shape_val_denot` (line 171-179 of Core.lean) shows:
```lean
| env, .arrow T1 T2 => fun A H e =>
  ∃ T0 t0,
    resolve H e = some (.abs T0 t0) ∧
    (∀ (arg : Nat) (H' : Heap),
      H'.subsumes H ->
      Ty.capt_val_denot env T1 H' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg (T1.captureSet.denot env))
        T2 A H' (t0.subst (Subst.openVar (.free arg))))
```

The existential introduces `T0` and `t0`, not `T1` and `e`. The proof should be restructuring the goal to match this denotation structure.

### Suggested Fix Strategy

Looking at the goal state after line 81, we need to provide:
1. A type `T0 : Ty .capt []`
2. An expression `t0 : Exp ([],x)`
3. Proof that `resolve store (.var (...)) = some (.abs T0 t0)`
4. The function property

The issue is we're trying to use the polymorphic `T1` and `e` directly, but after substitution these become concrete terms. We need to compute what they substitute to.

**Recommended approach**:
```lean
-- After: simp [Ty.exi_exp_denot, Ty.capt_val_denot, Ty.shape_val_denot]
-- The goal should show the arrow denotation structure
-- Instead of 'use T1, e', we need to show what T1 and e become after subst
constructor  -- for Eval
· -- Show (.abs T1 e).subst ... is a value
  simp [Exp.subst]
  constructor
· -- Show the denotation
  use (T1.subst (Subst.from_TypeEnv env)), (e.subst (Subst.from_TypeEnv env).lift)
  -- Then continue with the proof...
```

Actually, looking more carefully: The `Exp.subst` on line 80 probably already handles this. The real issue might be in how we're destructuring the goal. Let me reconsider...

After `apply Eval.eval_val` and proving the value case, we need to prove `Denot.as_post` holds. Let's check what that means and match the arrow denotation structure exactly.

## Remaining Work (50+ errors)

### High Priority - Core Typing Rules

1. **sem_typ_tabs** (lines 93-114)
   - Add capture sets to notation
   - Use sort-specific denotations
   - Handle PreDenot for type bounds

2. **sem_typ_app** (lines 199-225)
   - Add capture sets
   - Fix type sorts in arrow types

3. **sem_typ_tapp** (lines 227-251)
   - Add capture sets
   - Fix poly type handling

4. **sem_typ_letin** (lines 253-364)
   - Add capture sets
   - Handle existential types properly

### Medium Priority - Inversion Lemmas

5. **abs_val_denot_inv** (lines 116-141)
   - Use `Ty.shape_val_denot` for arrow type
   - Use `Ty.capt_val_denot` for argument type
   - Use `Ty.exi_exp_denot` for body type
   - Fix Cell constructor (use `Cell.abs` not `⟨.abs T0 e0, hv⟩`)

6. **tabs_val_denot_inv** (lines 143-179)
   - Similar fixes for poly types
   - Use PreDenot for bounds

7. **interp_var_subst** (line 181-183)
   - Extract `.1` from `interp_var env x`

8. **var_exp_denot_inv** (lines 185-191)
   - Use sort-specific exp/val denot

### Medium Priority - Helper Theorems

9. **typed_env_lookup_tvar** (lines 366-412)
   - Use `Ty.shape_val_denot` for type bounds
   - Fix EnvTyping destructuring (it's not a simple product type)
   - Handle `.cvar` case in there branch

### High Priority - Subtyping

10. **sem_subtyp_poly** (lines 414-450)
    - Types should be `.shape` -> `.exi`, not `.shape` -> `.shape`
    - Arrow body is `.exi` not `.shape`

11. **sem_subtyp_arrow** (lines 452-476)
    - Arrow takes `.capt` types not `.shape`
    - Context extension needs capture type

12. **Other subtyping lemmas** (lines 478-518)
    - Use `Ty.shape_val_denot` consistently
    - Fix goal structures to match CC denotations

### Low Priority - Fundamental Theorems

13. **fundamental_subtyp** (lines 509-518)
    - May need `cases` instead of `induction` (error about TySort.shape)

14. **sem_typ_subtyp** (lines 520-530)
    - Add capture sets

15. **fundamental** (lines 532-539)
    - Add capture sets
    - May need new cases for CC-specific constructs (cabs, capp, pack, unpack)

## Systematic Fixing Strategy

### Phase 1: Core Infrastructure (IN PROGRESS)
1. ✅ Fix typed_env_lookup_var
2. ✅ Fix sem_typ_var
3. 🔄 Fix sem_typ_abs (CURRENT)
4. Fix sem_typ_tabs
5. Fix sem_typ_app, sem_typ_tapp, sem_typ_letin

### Phase 2: Inversion Lemmas
6. Fix all `*_val_denot_inv` lemmas
7. Fix `interp_var_subst` and `var_exp_denot_inv`

### Phase 3: Subtyping
8. Fix all `sem_subtyp_*` lemmas
9. Fix `fundamental_subtyp`

### Phase 4: Top-Level Theorems
10. Fix `sem_typ_subtyp` and `fundamental`
11. Add proofs for CC-specific constructs (cabs, capp, pack, unpack)

### Phase 5: Verification
12. Run final `lean4check`
13. Address any remaining warnings

## Key Patterns for Fixing

### Pattern 1: Adding Capture Sets
```lean
-- Before (Fsub):
theorem sem_typ_foo (ht : Γ ⊨ e : T) : ...

-- After (CC):
theorem sem_typ_foo (ht : C # Γ ⊨ e : T) : ...
```

### Pattern 2: Sort-Specific Denotations
```lean
-- Before (Fsub):
Ty.val_denot env T

-- After (CC) - depends on T's sort:
Ty.shape_val_denot env T  -- if T : Ty .shape s
Ty.capt_val_denot env T   -- if T : Ty .capt s
Ty.exi_val_denot env T    -- if T : Ty .exi s
```

### Pattern 3: Variable Lookup
```lean
-- Before (Fsub):
env.lookup_var x

-- After (CC):
(env.lookup_var x).1  -- extract Nat component
```

### Pattern 4: Environment Extension
```lean
-- Before (Fsub):
env.extend_var arg

-- After (CC):
env.extend_var arg (T.captureSet.denot env)
```

### Pattern 5: Weakening Lemmas
```lean
-- For .var binding:
weaken_capt_val_denot (env:=env0) (x:=n) (A:=capset) (T:=T0)

-- For .tvar binding:
tweaken_capt_val_denot (env:=env0) (d:=denot) (T:=T0)

-- For .cvar binding (NEW):
cweaken_capt_val_denot (env:=env0) (c:=capset) (T:=T0)
```

### Pattern 6: Type Constructors
```lean
-- Arrow needs .capt types:
.arrow (T1 : Ty .capt s) (T2 : Ty .exi (s,x)) : Ty .shape s

-- Wrap in .capt for capturing type:
.capt C (.arrow T1 T2) : Ty .capt s

-- Wrap in .typ for existential:
.typ (.capt C (.arrow T1 T2)) : Ty .exi s
```

### Pattern 7: Case Analysis on Bindings
```lean
cases binding
case var =>
  rename_i T_arg
  -- handle variable binding
case tvar =>
  rename_i S_bound
  -- handle type variable binding
case cvar =>  -- NEW - always needed
  rename_i B_bound
  -- handle capture variable binding
```

## Common Errors and Solutions

### Error: Unknown constant `CC.Ty.val_denot`
**Solution**: Replace with sort-specific version based on type sort

### Error: Invalid argument name `access` for `weaken_capt_val_denot`
**Solution**: Parameter is named `A` not `access`

### Error: Application type mismatch - `Nat × CapabilitySet` vs `Nat`
**Solution**: Extract first component: `(env.lookup_var x).1`

### Error: Type mismatch - `Ty .shape` expected but `Ty .capt` provided
**Solution**: Check type constructor requirements:
- `.arrow` takes `.capt` for argument, `.exi` for body
- `.poly` takes `.shape` for bound, `.exi` for body

### Error: Invalid `⟨...⟩` notation for Cell
**Solution**: Use explicit constructor: `Cell.abs T e` not `⟨.abs T e, hv⟩`

### Error: Unexpected token '⊨'
**Solution**: Add capture set parameter: `C # Γ ⊨ e : T`

## Reference Files

- **Onboarding**: `/Users/linyxus/Workspace/semantic/CLAUDE.md`
- **Denotation definitions**: `Semantic/CC/Denotation/Core.lean` (lines 160-210)
- **Weakening lemmas**: `Semantic/CC/Denotation/Rebind.lean` (lines 267-301)
- **Monotonicity (reference)**: `Semantic/CC/Denotation/Core.lean` (lines 307-562)
- **Fsub reference**: `Semantic/Fsub/Soundness.lean`

## Next Steps

1. **Immediate**: Fix `sem_typ_abs` proof body
   - Understand exact goal state after `apply Eval.eval_val`
   - Match arrow denotation structure from Core.lean:171-179
   - Handle or work around missing `Exp.from_TypeEnv_weaken_open` lemma

2. **Short-term**: Fix core typing rules (tabs, app, tapp, letin)

3. **Medium-term**: Fix inversion and subtyping lemmas

4. **Long-term**: Add CC-specific construct proofs (cabs, capp, pack, unpack)

## Tips for Future Sessions

1. **Always run `lean4check` frequently** - don't accumulate errors
2. **Read error messages carefully** - they often indicate exactly which sort is expected
3. **Consult Core.lean denotation definitions** when unsure about structure
4. **Use `trace_state` tactic** to inspect goal state
5. **Use `rename_i` for unnamed variables** (marked with `✝`)
6. **Never guess - ultrathink and understand** the type system deeply
7. **Match denotation structures exactly** - existentials, functions, etc.
8. **Remember: Shape types return PreDenot** (take capability set parameter)
