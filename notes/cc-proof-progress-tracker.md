# CC Soundness Porting Status

**Last Updated**: 2025-10-24 (Session 3)
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

## Session 3 Progress: Three Abstractions Complete

**Date**: 2025-10-24
**Focus**: Complete all three abstraction forms (term, type, capture)

### Key Discovery: Capability Set Handling Differs by Abstraction Type

The three abstraction forms in CC handle capability sets differently, reflecting their semantic roles:

| Abstraction | Capability Set for Body | Semantic Reason |
|-------------|------------------------|-----------------|
| `abs` (term) | `A ∪ T1.captureSet` | Body needs function's captures AND parameter's capabilities |
| `tabs` (type) | `A` only | Type parameters don't carry runtime capabilities |
| `cabs` (capture) | `A` only | Capture parameters are constraints, not new capabilities |

**Why this matters**: Term abstractions are special because their parameters carry **runtime capabilities**. Type and capture abstractions deal with compile-time information only.

### ⚠️ sem_typ_app (Soundness.lean:343-353)

**Status**: Incomplete - left with `sorry` and detailed comment

**Helper lemmas proved** (Soundness.lean:222-306):

```lean
-- Inverts arrow type to extract function properties
theorem abs_val_denot_inv {A : CapabilitySet}
  (hv : Ty.shape_val_denot env (.arrow T1 T2) A store (.var x)) :
  ∃ fx, x = .free fx ∧ ∃ T0 e0,
    store fx = some (.val ⟨.abs T0 e0, by constructor⟩) ∧
    (∀ (H' : Heap) (arg : Nat), ...)

-- Extracts value denotation from expression denotation
theorem var_exp_denot_inv {A : CapabilitySet}
  (hv : Ty.exi_exp_denot env T A store (.var x)) :
  Ty.exi_val_denot env T store (.var x)

-- Shows substituted bound variables become free
theorem var_subst_is_free {x : BVar s .var} :
  ∃ fx, (Subst.from_TypeEnv env).var x = .free fx

-- Empty-signature variables are free
theorem closed_var_inv (x : Var .var {}) :
  ∃ fx, x = .free fx
```

**Next steps for completion**:
- May need lemmas to extract `Ty.exi_exp_denot` from `Eval` goals
- Need better handling of variable substitution in arbitrary signatures
- Consider proving a more general "opening lemma" that works with `Var` not just `BVar`

## Remaining Work (~45 errors)

### High Priority - Core Typing Rules

1. ✅ **sem_typ_tabs** - **COMPLETED in Session 3**

2. ✅ **sem_typ_cabs** - **COMPLETED in Session 3**

3. ⚠️ **sem_typ_app** (lines 343-353) - **PARTIAL PROGRESS in Session 3**
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

### Phase 1: Core Infrastructure ✅ **COMPLETED (Session 2)**
1. ✅ Fix typed_env_lookup_var
2. ✅ Fix sem_typ_var
3. ✅ Fix sem_typ_abs (including arrow denotation fix)
4. ✅ Prove substitution lemmas for term variables
5. ✅ Fix Rebind and Retype proofs

### Phase 2: Core Typing Rules ✅ **MOSTLY COMPLETED (Session 3)**
1. ✅ Prove substitution lemmas for type variables
2. ✅ Prove substitution lemmas for capture variables
3. ✅ Fix sem_typ_tabs
4. ✅ Fix sem_typ_cabs
5. ⚠️ Fix sem_typ_app (partial - helper lemmas done, main proof needs work)
6. TODO: Fix sem_typ_tapp, sem_typ_letin

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

### Pattern 8: **Capability Set Unioning in Arrow Bodies**
```lean
-- When proving properties about arrow bodies, remember:
-- The body is evaluated with A ∪ T1.captureSet.denot env

-- In rebind/retype proofs:
exact (ih2 (A ∪ capset) H' _).mp hd

-- In sem_typ_abs proof:
-- Show: (Cf.rename Rename.succ ∪ .var .here).denot env'
--     = Cf.denot env ∪ param_capset
```

### Pattern 9: **Three Abstraction Forms Have Different Capability Handling**
```lean
-- Term abstraction (abs): Body gets A ∪ param_capabilities
theorem sem_typ_abs
  (ht : (Cf.rename Rename.succ ∪ .var (.bound .here)) # Γ,x:T1 ⊨ e : T2) :
  ∅ # Γ ⊨ Exp.abs T1 e : .typ (Ty.capt Cf (T1.arrow T2))
-- Proof uses: env.extend_var arg (T1.captureSet.denot env)
-- Arrow body evaluated with: A ∪ T1.captureSet.denot env

-- Type abstraction (tabs): Body gets A only
theorem sem_typ_tabs
  (ht : Cf.rename Rename.succ # (Γ,X<:S) ⊨ e : T) :
  ∅ # Γ ⊨ Exp.tabs S e : .typ (Ty.capt Cf (S.poly T))
-- Proof uses: env.extend_tvar denot
-- Poly body evaluated with: A (no unioning)
-- Uses: Exp.from_TypeEnv_weaken_open_tvar

-- Capture abstraction (cabs): Body gets A only
theorem sem_typ_cabs
  (ht : Cf.rename Rename.succ # Γ,C<:cb ⊨ e : T) :
  ∅ # Γ ⊨ Exp.cabs cb e : .typ (Ty.capt Cf (Ty.cpoly cb T))
-- Proof uses: env.extend_cvar A0 (where A0 ⊆ cb.denot env)
-- Cpoly body evaluated with: A (no unioning)
-- Uses: Exp.from_TypeEnv_weaken_open_cvar
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

### Session 2: Arrow Denotation and Infrastructure

#### 1. **Arrow Denotation Must Union Capability Sets**
The initial naive port appeared unprovable because the arrow denotation was missing the union. The semantic intuition is clear: when you call a function that captures capabilities `A` with an argument that carries capabilities `B`, the function body should have access to `A ∪ B`.

#### 2. **Rebind/Retype Lemmas Must Respect the Denotation Structure**
When the arrow denotation changed to union capability sets, the rebind and retype preservation lemmas had to be updated to match. This is a general principle: **structural lemmas must exactly match the semantic definitions**.

#### 3. **Substitution Lemmas Bridge Syntax and Semantics**
The `from_TypeEnv_weaken_open` lemmas show how syntactic operations (opening binders) correspond to semantic operations (extending environments). These bridges are essential for soundness proofs.

#### 4. **Capture Set Renaming Preserves Denotations**
The `rebind_captureset_denot` lemma is crucial for showing that weakening (renaming) preserves the meaning of capture sets. Used extensively in all abstraction proofs.

### Session 3: Three Abstraction Forms

#### 5. **Abstraction Forms Differ in Capability Handling Based on Runtime vs Compile-Time**
The key insight: Only **term abstractions** union capability sets because only term parameters carry runtime capabilities. Type parameters and capture parameters are compile-time constructs that don't contribute new runtime capabilities.

**Consequence**: When porting proofs, always check which abstraction form you're working with:
- `abs`: Use `A ∪ T.captureSet.denot env`, need parameter capability access
- `tabs`/`cabs`: Use just `A`, no capability unioning needed

#### 6. **Each Binding Kind Needs Its Own Substitution Lemmas**
Pattern emerged: For each binding kind (`.var`, `.tvar`, `.cvar`), we need:
- A `Subst.from_TypeEnv_weaken_open_*` lemma
- An `Exp.from_TypeEnv_weaken_open_*` lemma
- A `Rebind.*weaken` lemma for capability set renaming

These form a complete set for reasoning about that binding kind.

#### 7. **Non-Empty Signatures Complicate Application Proofs**
Unlike Fsub where expressions are closed (`{}`), CC allows expressions in arbitrary contexts. This means:
- Variables may be bound, not just free
- Substitution must be tracked through non-empty environments
- Need more sophisticated lemmas to bridge `Var` and `BVar` handling

#### 8. **Helper Lemmas Must Preserve Sort Information**
The `abs_val_denot_inv` and similar inversion lemmas must carefully preserve type sort information (`.shape`, `.capt`, `.exi`). Getting the sorts wrong makes the lemma unusable.

## Reference Files

- **Onboarding**: `/Users/linyxus/Workspace/semantic/CLAUDE.md`
- **Denotation definitions**: `Semantic/CC/Denotation/Core.lean` (lines 160-210)
- **Substitution lemmas**: `Semantic/CC/Denotation/Core.lean` (lines 274-292)
- **Weakening lemmas**: `Semantic/CC/Denotation/Rebind.lean` (lines 40-60, 267-301)
- **Monotonicity (reference)**: `Semantic/CC/Denotation/Core.lean` (lines 307-562)
- **Fsub reference**: `Semantic/Fsub/Soundness.lean`

## Next Steps

1. **Immediate**: Complete `sem_typ_app`
   - Helper lemmas are in place
   - Main challenge: handling non-empty signatures correctly
   - May need additional bridging lemmas between `Var` and `BVar`
   - Consider looking at how Fsub handles this (though it's simpler with empty signatures)

2. **Short-term**: Port `sem_typ_tapp` and `sem_typ_capp`
   - Type application (tapp) should follow tabs pattern
   - Capture application (capp) should follow cabs pattern
   - Both should be straightforward given the abstraction proofs

3. **Short-term**: Port `sem_typ_letin` and `sem_typ_unpack`
   - More complex environment manipulation
   - Build on existing substitution lemmas

4. **Medium-term**: Fix inversion and subtyping lemmas
   - Should be more straightforward now that core infrastructure is solid
   - May benefit from the helper lemmas already proved

5. **Long-term**: Complete `fundamental` theorem
   - Integrate all completed typing rules
   - Handle CC-specific cases (pack, invoke, etc.)

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

### Session 3 (Current)
```bash
✔ [3110/3110] Built Semantic.CC (2.2s)
✔ Built Semantic (2.2s)
Build completed successfully (3110 jobs)

⚠ 2 declarations use 'sorry':
  - sem_typ_app (lines 343-353) - partial progress, helper lemmas complete
  - fundamental (expected - waiting on remaining typing rules)
```

**Progress Summary**:
- ✅ **3 abstraction forms complete**: abs, tabs, cabs
- ✅ **All substitution lemmas proved**: term, type, and capture variables
- ✅ **Helper lemmas for application ready**: abs_val_denot_inv, var_exp_denot_inv, etc.
- ⚠️ **1 partially complete**: sem_typ_app (needs signature handling work)
- 📊 **Estimated ~40-45 theorems remaining**

**Key Achievement**: All three abstraction forms (term, type, capture) are now complete with full understanding of their different capability handling semantics. The infrastructure for application rules is largely in place.

Ready to continue with application rules and then subtyping! 🎯
