# Type Hierarchy Collapse in Capybara Module

## Overview

The Capybara module underwent a type hierarchy simplification: the `.shape` sort was eliminated, merging all types into `.capt`. Capture sets are now embedded directly in type constructors rather than wrapped via a separate `Ty.capt` constructor.

## Current Status (Branch: no-capt-types)

**All core denotation files compile cleanly:**
- `Semantic/Capybara/Denotation/Core.lean`
- `Semantic/Capybara/Denotation/Rebind.lean`
- `Semantic/Capybara/Denotation/Retype.lean`
- `Semantic/Capybara/Fundamental.lean` (var case proven, others pending)

## Type System Changes

### Before (CC module style)
```lean
inductive TySort : Type where
| capt : TySort    -- capturing types
| shape : TySort   -- shape types
| exi : TySort     -- existential types

inductive Ty : TySort -> Sig -> Type where
| capt : CaptureSet s -> Ty .shape s -> Ty .capt s  -- wrapper
-- shape types produced Ty .shape s
```

### After (Capybara module)
```lean
inductive TySort : Type where
| capt : TySort    -- all regular types (NO .shape!)
| exi : TySort     -- existential types

inductive Ty : TySort -> Sig -> Type where
| top : Ty .capt s
| tvar : BVar s .tvar -> Ty .capt s
| arrow : Ty .capt s -> CaptureSet s -> Ty .exi (s,x) -> Ty .capt s
| poly : Ty .capt s -> CaptureSet s -> Ty .exi (s,X) -> Ty .capt s
| cpoly : Mutability -> CaptureSet s -> Ty .exi (s,C) -> Ty .capt s
| cap : CaptureSet s -> Ty .capt s
| cell : CaptureSet s -> Ty .capt s
| reader : CaptureSet s -> Ty .capt s
| unit : Ty .capt s
| bool : Ty .capt s
| exi : Ty .capt (s,C) -> Ty .exi s
| typ : Ty .capt s -> Ty .exi s
-- NO Ty.capt wrapper constructor!
```

Key: Capture sets embedded directly in `arrow`, `poly`, `cpoly`, `cap`, `cell`, `reader`.

## Denotation Architecture

### Key Types
```lean
abbrev Denot := Memory -> Exp {} -> Prop
abbrev CapabilitySet := Set (Mutability × Nat)  -- ground, no signature param
abbrev PreDenot := CapabilitySet -> Memory -> Exp {} -> Prop
```

### Expression Denotations Take CapabilitySet (Not CaptureSet)
```lean
def Ty.exp_denot : TypeEnv s -> Ty .capt s -> PreDenot
| ρ, T, R => fun m e => Eval R m e (Ty.val_denot ρ T).as_mpost

def Ty.exi_exp_denot : TypeEnv s -> Ty .exi s -> PreDenot
| ρ, T, R => fun m e => Eval R m e (Ty.exi_val_denot ρ T).as_mpost
```

The `R : CapabilitySet` is a **ground** capability set (no signature parameter).

### Body Conditions in val_denot Use Ground R0

For arrow/poly/cpoly, body conditions use `R0 := expand_captures m.heap cs'`:

```lean
| env, .arrow T1 cs T2 => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ cs' T0 t0,
    resolve m.heap e = some (.abs cs' T0 t0) ∧
    cs'.WfInHeap m.heap ∧
    let R0 := expand_captures m.heap cs'
    R0 ⊆ (cs.denot env m) ∧
    (∀ (arg : Nat) (m' : Memory),
      m'.subsumes m ->
      Ty.val_denot env T1 m' (.var (.free arg)) ->
      Ty.exi_exp_denot
        (env.extend_var arg (compute_peakset env T1.captureSet))
        T2
        (R0 ∪ (reachability_of_loc m'.heap arg))  -- ground CapabilitySet!
        m' (t0.subst (Subst.openVar (.free arg))))
```

For poly/cpoly, body uses just `R0` (no union with reachability).

### SemanticTyping Converts CaptureSet to CapabilitySet
```lean
def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ m,
    EnvTyping Γ ρ m ->
    Ty.exi_exp_denot ρ E (C.denot ρ m) m (e.subst (Subst.from_TypeEnv ρ))
```

## Key Theorems

### val_denot_refine (Core.lean:2643)
Transforms value denotation for `T` to `T.refineCaptureSet`:
```lean
theorem val_denot_refine {env : TypeEnv s} {T : Ty .capt s} {x : Var .var s}
  (hdenot : (Ty.val_denot env T) m (.var (x.subst (Subst.from_TypeEnv env)))) :
  (Ty.val_denot env (T.refineCaptureSet (.var .epsilon x)))
    m (.var (x.subst (Subst.from_TypeEnv env)))
```

### Rebind/Retype Theorems (Simplified)
Since `R : CapabilitySet` is ground, rebinding/retyping doesn't change it:
```lean
def rebind_exp_denot (ρ : Rebind env1 f env2) (T : Ty .capt s1) (R : CapabilitySet) :
  Ty.exp_denot env1 T R ≈ Ty.exp_denot env2 (T.rename f) R

def retype_exp_denot (ρ : Retype env1 σ env2) (T : Ty .capt s1) (R : CapabilitySet) :
  Ty.exp_denot env1 T R ≈ Ty.exp_denot env2 (T.subst σ) R
```

Body conditions in rebind_val_denot/retype_val_denot just pass `R0` directly (no CaptureSet renaming/substitution needed).

## Fundamental Theorem Progress

### Proven Cases
- **var**: Uses `sem_typ_var` which applies `typed_env_lookup_var` + `val_denot_refine`

### sem_typ_var Structure
```lean
theorem sem_typ_var (hx : Γ.LookupVar x T) :
  (.var .epsilon (.bound x)) # Γ ⊨ (Exp.var (.bound x)) :
    (.typ (T.refineCaptureSet (.var .epsilon (.bound x)))) := by
  intro env m hts
  simp only [Ty.exi_exp_denot, Ty.exi_val_denot]
  apply Eval.eval_var
  simp only [Denot.as_mpost]
  have h_lookup := typed_env_lookup_var hts hx
  have h_refined := val_denot_refine (x := .bound x) h_lookup
  simp only [Var.subst, Subst.from_TypeEnv] at h_refined
  exact h_refined
```

## Common Patterns

### 1. Body Conditions Use Ground CapabilitySet
```lean
-- In rebind_val_denot/retype_val_denot arrow case:
let R0 := expand_captures m.heap cs'
have ih2 := rebind_exi_exp_denot (ρ.liftVar ...) T2
  (R0 ∪ (reachability_of_loc m'.heap arg))  -- pass ground set directly
exact (ih2 m' _).mp hd

-- For poly/cpoly, just R0:
have ih2 := rebind_exi_exp_denot (ρ.liftTVar ...) T2 R0
```

### 2. Explicit Kind Annotations
```lean
-- For arrow: (k:=.var)
cs.rename (Rename.succ (k:=.var))

-- For poly: (k:=.tvar)
cs.rename (Rename.succ (k:=.tvar))

-- For cpoly: (k:=.cvar)
cs.rename (Rename.succ (k:=.cvar))
```

### 3. Removed Definitions
These are commented out in Core.lean (no longer needed):
- `Ty.shape_val_denot`, `Ty.capt_val_denot` (replaced by `Ty.val_denot`)
- `Denot.is_reachability_safe/monotonic/tight`
- `TypeEnv.is_reachability_safe/monotonic/tight`
- Related `*_is_tight`, `*_is_monotonic` theorems

## Tips

1. Use `lean4check` (not `lake build`) for better diagnostics
2. Use `trace_state` to inspect goal context
3. Variables with `✝` suffix are unnamed - use `rename_i` (names from bottom of context)
4. `CapabilitySet` is ground - no need for renaming/substitution in rebind/retype proofs
