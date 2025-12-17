# Type Hierarchy Collapse in Capybara Module

## Overview

The Capybara module underwent a type hierarchy simplification: the `.shape` sort was eliminated, merging all types into `.capt`. Capture sets are now embedded directly in type constructors rather than wrapped via a separate `Ty.capt` constructor.

## Type System Changes

### Before (CC module style)
```lean
inductive TySort : Type where
| capt : TySort    -- capturing types
| shape : TySort   -- shape types
| exi : TySort     -- existential types

inductive Ty : TySort -> Sig -> Type where
-- shape types
| top : Ty .shape s
| arrow : Ty .capt s -> Ty .exi (s,x) -> Ty .shape s
| poly : Ty .shape s -> Ty .exi (s,X) -> Ty .shape s
| cpoly : CaptureBound s -> Ty .exi (s,C) -> Ty .shape s
-- capturing types (wraps shape + capture set)
| capt : CaptureSet s -> Ty .shape s -> Ty .capt s
-- existential types
| exi : Ty .capt (s,C) -> Ty .exi s
| typ : Ty .capt s -> Ty .exi s
```

### After (Capybara module)
```lean
inductive TySort : Type where
| capt : TySort    -- all regular types
| exi : TySort     -- existential types
-- NO .shape sort!

inductive Ty : TySort -> Sig -> Type where
-- All former "shape" types now directly produce .capt, with embedded capture sets
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
-- NO Ty.capt constructor!
-- existential types
| exi : Ty .capt (s,C) -> Ty .exi s
| typ : Ty .capt s -> Ty .exi s
```

Key differences:
1. No `.shape` sort - everything is `.capt` or `.exi`
2. No `Ty.capt` wrapper constructor
3. Capture sets embedded in `arrow`, `poly`, `cpoly`, `cap`, `cell`, `reader`
4. `cpoly` takes `Mutability` instead of `CaptureBound`

## Denotation Changes

### Before
```lean
-- Separate denotations for shape and capturing types
def Ty.shape_val_denot : TypeEnv s -> Ty .shape s -> PreDenot
def Ty.capt_val_denot : TypeEnv s -> Ty .capt s -> Denot

-- PreDenot vs Denot distinction
abbrev PreDenot := Memory -> Exp {} -> Prop
abbrev Denot := Memory -> Exp {} -> Prop
```

### After
```lean
-- Single unified denotation
def Ty.val_denot : TypeEnv s -> Ty .capt s -> Denot

-- Denot is the only type
abbrev Denot := Memory -> Exp {} -> Prop

-- TypeEnv stores Denot (not PreDenot) for type variables
structure TypeEnv (s : Sig) where
  ...
  tvar : ∀ X : BVar s .tvar, Denot  -- was PreDenot
```

### Denotation for arrow/poly/cpoly types

The denotation now handles embedded capture sets. Example for `arrow T1 cs T2`:

```lean
| env, .arrow T1 cs T2 => fun m e =>
  e.WfInHeap m.heap ∧
  (cs.subst (Subst.from_TypeEnv env)).WfInHeap m.heap ∧
  ∃ cs' x0 t0,
    resolve m.heap e = some (Exp.abs cs' x0 t0) ∧
    cs'.WfInHeap m.heap ∧
    expand_captures m.heap cs' ⊆ CaptureSet.denot env cs m ∧
    ∀ (m' : Memory) e' (hwf : e'.WfInHeap m'.heap),
      m'.subsumes m ->
      Ty.val_denot env T1 m' e' ->
      Ty.exi_exp_denot (env.extend_var e' (Reachability.reachability_set m' e'))
        T2
        (cs.rename Rename.succ ∪ .var .epsilon (.bound .here))  -- NOTE: embedded cs
        m'
        (t0.subst (Subst.openVar e'))
```

## Files Status

### Repaired (compiles cleanly)
- `Semantic/Capybara/Denotation/Core.lean`
- `Semantic/Capybara/Denotation/Rebind.lean`

### Needs Repair
- `Semantic/Capybara/Denotation/Retype.lean` - uses old `Ty.shape_val_denot`, `PreDenot`

## Common Patterns for Repairs

### 1. Replace shape_val_denot/capt_val_denot with val_denot
```lean
-- Before
Ty.shape_val_denot env T
Ty.capt_val_denot env T

-- After
Ty.val_denot env T
```

### 2. Replace PreDenot with Denot
```lean
-- Before
{d : PreDenot}
env.extend_tvar d  -- took PreDenot

-- After
{d : Denot}
env.extend_tvar d  -- takes Denot
```

### 3. Explicit kind annotations for Rename.succ and f.lift

When working with capture sets in arrow/poly/cpoly cases, Lean cannot infer the `Kind` argument. Add explicit annotations:

```lean
-- For arrow (value variable): (k:=.var)
cs.rename (Rename.succ (k:=.var))
f.lift (k:=.var)

-- For poly (type variable): (k:=.tvar)
cs.rename (Rename.succ (k:=.tvar))
f.lift (k:=.tvar)

-- For cpoly (capture variable): (k:=.cvar)
cs.rename (Rename.succ (k:=.cvar))
f.lift (k:=.cvar)
```

### 4. Capture set renaming commutation

Use `CaptureSet.weaken_rename_comm` to prove:
```lean
(cs.rename Rename.succ).rename f.lift = (cs.rename f).rename Rename.succ
```

Full proof pattern:
```lean
have hcs_eq : (cs.rename (Rename.succ (k:=.var))).rename (f.lift (k:=.var)) =
              (cs.rename f).rename (Rename.succ (k:=.var)) :=
  CaptureSet.weaken_rename_comm
rw [hcs_eq] at ih
```

### 5. Removed definitions (commented out in Core.lean)

These are no longer needed without shape/capt split:
- `Denot.is_reachability_safe`
- `Denot.is_reachability_monotonic`
- `Denot.is_tight`
- `TypeEnv.is_reachability_safe`
- `TypeEnv.is_reachability_monotonic`
- `TypeEnv.is_tight`
- Related theorems: `typed_env_is_*`, `val_denot_is_*`, `shape_val_denot_is_*`

## Rebind.lean Structure

The rebind theorems relate type environments under renaming. Key mutual definitions:

```lean
mutual
def rebind_val_denot
  {s1 s2 : Sig} {env1 : TypeEnv s1} {f : Rename s1 s2} {env2 : TypeEnv s2}
  (ρ : Rebind env1 f env2) (T : Ty .capt s1) :
  Ty.val_denot env1 T ≈ Ty.val_denot env2 (T.rename f)

def rebind_exi_val_denot ...
def rebind_exp_denot ...
def rebind_exi_exp_denot ...
end
```

## Tips

1. Use `lean4check` frequently - it provides better diagnostics than `lake build`
2. Use `trace_state` tactic to inspect goal context when unsure
3. Named variables with `✝` suffix are unnamed - use `rename_i` to name them (names from bottom of context)
4. When in doubt about implicit arguments, add explicit type annotations
5. The `calc` mode helps with step-by-step equality transformations
