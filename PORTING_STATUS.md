# CC Soundness Porting Status

**Last Updated**: 2025-10-24 (Session 2)
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
Ty.exi_exp_denot   : TypeEnv s -> Ty .exi s -> PreDenot
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

### 8. **CRITICAL: Arrow Denotation and Capability Set Unioning**
The arrow denotation correctly **unions** capability sets when evaluating the function body:

```lean
| env, .arrow T1 T2 => fun A H e =>
  ∃ T0 t0,
    resolve H e = some (.abs T0 t0) ∧
    (∀ (arg : Nat) (H' : Heap),
      H'.subsumes H ->
      Ty.capt_val_denot env T1 H' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg (T1.captureSet.denot env))
        T2 (A ∪ T1.captureSet.denot env) H'  -- KEY: Union here!
        (t0.subst (Subst.openVar (.free arg))))
```

**Why this is necessary**: The function body `T2` should have access to:
- The capabilities captured by the arrow itself (`A`)
- The capabilities from the parameter (`T1.captureSet.denot env`)

This union is **semantically essential** - without it, the function body would be incorrectly restricted.

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

### ✅ sem_typ_abs (lines 93-134)
**Status**: ✅ **FULLY PORTED AND COMPILES**

**Signature**:
```lean
theorem sem_typ_abs {T2 : Ty TySort.exi (s,x)} {Cf : CaptureSet s}
  (ht : (Cf.rename Rename.succ ∪ .var (.bound .here)) # Γ,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs T1 e : .typ (Ty.capt Cf (T1.arrow T2))
```

**Key insights discovered**:

1. **The Arrow Denotation Fix (Core.lean:171-179)**
   - Initially appeared unprovable due to capability set mismatch
   - The fix: Arrow denotation now correctly unions `A ∪ T1.captureSet.denot env`
   - This makes the proof straightforward and semantically correct

2. **Substitution Lemmas Required (Core.lean:274-292)**
   - Proved `Subst.from_TypeEnv_weaken_open`: Composition of lift and opening
   - Proved `Exp.from_TypeEnv_weaken_open`: Expression substitution over opening
   - These lemmas bridge the gap between syntactic and semantic variable binding

3. **Capability Set Equation**:
   ```lean
   (Cf.rename Rename.succ ∪ .var (.bound .here)).denot (env.extend_var arg A)
   = Cf.denot env ∪ A
   ```
   Where:
   - `Cf.rename Rename.succ` denotes to `Cf.denot env` (via `rebind_captureset_denot`)
   - `.var (.bound .here)` denotes to the freshly added capability set `A`
   - Their union matches **exactly** what the arrow denotation expects!

4. **Proof Structure**:
   ```lean
   intro env store hts
   simp [Ty.exi_exp_denot, Ty.exi_val_denot, Ty.capt_val_denot, Ty.shape_val_denot]
   apply Eval.eval_val
   · simp [Exp.subst]; constructor  -- Show it's a value
   · simp [Denot.as_post]
     -- Provide the existential witnesses
     use (T1.subst (Subst.from_TypeEnv env)), (e.subst (Subst.from_TypeEnv env).lift)
     constructor
     · simp [resolve, Exp.subst]  -- resolve returns the abstraction
     · -- The function property: prove body typechecks with unioned capabilities
       intro arg H' hsubsume harg
       rw [Exp.from_TypeEnv_weaken_open (A := T1.captureSet.denot env)]
       -- Build extended environment typing
       have henv : EnvTyping (Γ,x:T1) (env.extend_var arg ...) H' := ...
       have this := ht (env.extend_var arg ...) H' henv
       -- Show capability sets align using rebind lemmas
       have hcap_rename := rebind_captureset_denot (Rebind.weaken ...) Cf
       have hcap_var : ... := by simp [CaptureSet.denot, ...]
       rw [← hcap_rename, ← hcap_var]
       simp [CaptureSet.denot]
       exact this
   ```

### ✅ Substitution Lemmas (Core.lean:274-292)
**Status**: Proved and verified

These lemmas were commented out but are essential for sem_typ_abs:

```lean
theorem Subst.from_TypeEnv_weaken_open {env : TypeEnv s} {x : Nat} {A : CapabilitySet} :
  (Subst.from_TypeEnv env).lift.comp (Subst.openVar (.free x)) =
    Subst.from_TypeEnv (env.extend_var x A)

theorem Exp.from_TypeEnv_weaken_open
  {env : TypeEnv s} {x : Nat} {A : CapabilitySet} {e : Exp (s,x)} :
  (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free x)) =
    e.subst (Subst.from_TypeEnv (env.extend_var x A))
```

**Why they matter**: These lemmas show that variable opening commutes with environment extension, which is crucial for reasoning about function application semantics.

### ✅ Rebind Proofs Fixed (Rebind.lean:99-131)
**Status**: Fixed to account for capability set unioning

The `rebind_shape_val_denot` proof for arrow case now correctly applies the inductive hypothesis with the **unioned capability set**:

```lean
case arrow T1 T2 => by
  -- Forward direction (line 117):
  exact (ih2 (A ∪ (C.rename f).denot env2) H' _).mp hd

  -- Backward direction (line 131):
  exact (ih2 (A ∪ C.denot env1) H' _).mpr hd
```

**Key insight**: When showing that renaming preserves arrow denotations, we must account for the fact that the arrow body is evaluated with `A ∪ capset`, not just `A`.

### ✅ Retype Proofs Fixed (Retype.lean:149-183)
**Status**: Fixed to account for capability set unioning

Similar fix for substitution preservation:

```lean
case arrow T1 T2 => by
  -- Forward direction (line 167):
  exact (ih2 (A ∪ (C.subst σ).denot env2) H' _).mp hd

  -- Backward direction (line 181):
  have := (ih2 (A ∪ (C.subst σ).denot env2) H' _).mpr hd
```

## Remaining Work (~50 errors)

### High Priority - Core Typing Rules

1. **sem_typ_tabs** (lines 114-119, commented out)
   - Add capture sets to notation
   - Use sort-specific denotations
   - Handle PreDenot for type bounds
   - Similar structure to sem_typ_abs but for type abstraction

2. **sem_typ_app** (lines 199-225)
   - Add capture sets
   - Fix type sorts in arrow types
   - Handle function application with capability flow

3. **sem_typ_tapp** (lines 227-251)
   - Add capture sets
   - Fix poly type handling
   - Handle type application

4. **sem_typ_letin** (lines 253-364)
   - Add capture sets
   - Handle existential types properly
   - Complex proof with environment extension

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

### Phase 1: Core Infrastructure ✅ **COMPLETED**
1. ✅ Fix typed_env_lookup_var
2. ✅ Fix sem_typ_var
3. ✅ Fix sem_typ_abs (including arrow denotation fix)
4. ✅ Prove substitution lemmas
5. ✅ Fix Rebind and Retype proofs

### Phase 2: Core Typing Rules (NEXT)
4. Fix sem_typ_tabs
5. Fix sem_typ_app, sem_typ_tapp, sem_typ_letin

### Phase 3: Inversion Lemmas
6. Fix all `*_val_denot_inv` lemmas
7. Fix `interp_var_subst` and `var_exp_denot_inv`

### Phase 4: Subtyping
8. Fix all `sem_subtyp_*` lemmas
9. Fix `fundamental_subtyp`

### Phase 5: Top-Level Theorems
10. Fix `sem_typ_subtyp` and `fundamental`
11. Add proofs for CC-specific constructs (cabs, capp, pack, unpack)

### Phase 6: Verification
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

### Pattern 8: **NEW - Capability Set Unioning in Arrow/Poly Bodies**
```lean
-- When proving properties about arrow bodies, remember:
-- The body is evaluated with A ∪ T1.captureSet.denot env

-- In rebind/retype proofs:
exact (ih2 (A ∪ capset) H' _).mp hd

-- In sem_typ_abs proof:
-- Show: (Cf.rename Rename.succ ∪ .var .here).denot env'
--     = Cf.denot env ∪ param_capset
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

### Error: Capability set mismatch in arrow body
**Solution**: Remember that arrow bodies are evaluated with **unioned** capability sets: `A ∪ T1.captureSet.denot env`

## Critical Lessons Learned

### 1. **Arrow Denotation Must Union Capability Sets**
The initial naive port appeared unprovable because the arrow denotation was missing the union. The semantic intuition is clear: when you call a function that captures capabilities `A` with an argument that carries capabilities `B`, the function body should have access to `A ∪ B`.

### 2. **Rebind/Retype Lemmas Must Respect the Denotation Structure**
When the arrow denotation changed to union capability sets, the rebind and retype preservation lemmas had to be updated to match. This is a general principle: **structural lemmas must exactly match the semantic definitions**.

### 3. **Substitution Lemmas Bridge Syntax and Semantics**
The `from_TypeEnv_weaken_open` lemmas show how syntactic operations (opening binders) correspond to semantic operations (extending environments). These bridges are essential for soundness proofs.

### 4. **Capture Set Renaming Preserves Denotations**
The `rebind_captureset_denot` lemma is crucial for showing that weakening (renaming) preserves the meaning of capture sets. Used extensively in sem_typ_abs.

## Reference Files

- **Onboarding**: `/Users/linyxus/Workspace/semantic/CLAUDE.md`
- **Denotation definitions**: `Semantic/CC/Denotation/Core.lean` (lines 160-210)
- **Substitution lemmas**: `Semantic/CC/Denotation/Core.lean` (lines 274-292)
- **Weakening lemmas**: `Semantic/CC/Denotation/Rebind.lean` (lines 40-60, 267-301)
- **Monotonicity (reference)**: `Semantic/CC/Denotation/Core.lean` (lines 307-562)
- **Fsub reference**: `Semantic/Fsub/Soundness.lean`

## Next Steps

1. **Immediate**: Port `sem_typ_tabs`
   - Very similar structure to `sem_typ_abs`
   - Type abstraction instead of term abstraction
   - No capability set unioning needed (just `A`)

2. **Short-term**: Fix core typing rules (app, tapp, letin)
   - These build on the abstraction rules
   - Will exercise the arrow denotation in application

3. **Medium-term**: Fix inversion and subtyping lemmas
   - Should be more straightforward now that core infrastructure is solid

4. **Long-term**: Add CC-specific construct proofs (cabs, capp, pack, unpack)
   - Capture polymorphism is unique to CC
   - Will need careful treatment

## Tips for Future Sessions

1. **Always run `lean4check` frequently** - don't accumulate errors
2. **Read error messages carefully** - they often indicate exactly which sort is expected
3. **Consult Core.lean denotation definitions** when unsure about structure
4. **Use `trace_state` tactic** to inspect goal state
5. **Use `rename_i` for unnamed variables** (marked with `✝`)
6. **Never guess - ultrathink and understand** the type system deeply
7. **Match denotation structures exactly** - existentials, functions, etc.
8. **Remember: Shape types return PreDenot** (take capability set parameter)
9. **Remember: Arrow bodies get unioned capability sets** (`A ∪ param_caps`)
10. **When updating denotations, update ALL dependent lemmas** (rebind, retype, proofs)

## Build Status

```bash
✔ [3084/3084] Built Semantic.CC.Soundness
⚠ warning: declaration uses 'sorry' (only in `fundamental` - expected)
Build completed successfully
```

All infrastructure is solid. Ready to proceed with remaining typing rules! 🎉
