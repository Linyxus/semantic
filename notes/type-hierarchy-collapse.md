# Type Hierarchy Collapse in Capybara Module

## Overview

The Capybara module underwent a type hierarchy simplification: the `.shape` sort was eliminated, merging all types into `.capt`. Capture sets are now embedded directly in type constructors rather than wrapped via a separate `Ty.capt` constructor.

## Current Status (Branch: no-capt-types)

**All files compile cleanly:**
- `Semantic/Capybara/Denotation/Core.lean`
- `Semantic/Capybara/Denotation/Rebind.lean`
- `Semantic/Capybara/Denotation/Retype.lean`
- `Semantic/Capybara/Fundamental.lean`

**Fundamental theorem progress:**
- Proven cases in `fundamental`: var, abs, tabs, cabs, app, tapp, capp, pack, unpack, subtyp
- All `fundamental_subtyp` cases proven: top, refl, trans, arrow, cpoly, poly, exi, typ
- Remaining: read, write, par, etc. (some depend on `sem_typ_par` which has sorry)

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

## Key Semantic Subtyping Lemmas

All updated for collapsed hierarchy. Note the patterns:

### sem_subtyp_arrow
```lean
lemma sem_subtyp_arrow {T1 T2 : Ty .capt s} {cs1 cs2 : CaptureSet s} {U1 U2 : Ty .exi (s,x)}
  (harg : SemSubtyp Γ T2 T1)           -- contravariant
  (hcs : SemSubcapt Γ cs1 cs2)         -- covariant
  (hcs2_closed : CaptureSet.IsClosed cs2)  -- closedness for wf monotonicity
  (hres : SemSubtyp (Γ,x:T2) U1 U2) :
  SemSubtyp Γ (.arrow T1 cs1 U1) (.arrow T2 cs2 U2)
```

### sem_subtyp_poly (uses PureTy.core)
```lean
lemma sem_subtyp_poly {S1 S2 : PureTy s} {cs1 cs2 : CaptureSet s} {T1 T2 : Ty .exi (s,X)}
  (hS : SemSubtyp Γ S2.core S1.core)   -- contravariant bounds
  (hcs : SemSubcapt Γ cs1 cs2)
  (hcs2_closed : CaptureSet.IsClosed cs2)
  (hT : SemSubtyp (Γ,X<:S2) T1 T2) :
  SemSubtyp Γ (.poly S1.core cs1 T1) (.poly S2.core cs2 T2)
```

### sem_subtyp_cpoly
```lean
lemma sem_subtyp_cpoly {m1 m2 : Mutability} {cs1 cs2 : CaptureSet s} {T1 T2 : Ty .exi (s,C)}
  (hB : m2 ≤ m1)                       -- contravariant mutability
  (hcs : SemSubcapt Γ cs1 cs2)
  (hcs2_closed : CaptureSet.IsClosed cs2)
  (hT : SemSubtyp (Γ,C<:m2) T1 T2) :
  SemSubtyp Γ (.cpoly m1 cs1 T1) (.cpoly m2 cs2 T2)
```

### sem_subtyp_trans/refl
Only handle `capt` and `exi` cases (no `shape`):
```lean
cases k with
| capt => ...
| exi => ...
```

## Key Patterns

### 1. Closedness Premise for Capture Set Well-formedness
When proving wf monotonicity for capture sets in subtyping:
```lean
(hcs2_closed : CaptureSet.IsClosed cs2)
-- Used as:
have hwf := CaptureSet.wf_of_closed hcs2_closed
have hwf_subst := CaptureSet.wf_subst hwf (from_TypeEnv_wf_in_heap hts)
exact CaptureSet.wf_monotonic hwf_subst hsub
```

### 2. val_denot_implies_wf for Extracting Well-formedness
Instead of case analysis on all `Ty .capt` constructors:
```lean
-- OLD (broken after collapse):
cases T with
| capt C_T S => ...  -- only handles old wrapper

-- NEW (works with all constructors):
have hwf_env : (env.extend_cvar CS).is_implying_wf := by
  intro X
  cases X with
  | there X' =>
    simp [TypeEnv.extend_cvar, TypeEnv.lookup_tvar]
    exact typed_env_is_implying_wf hts X'
have hwf_exp := val_denot_implies_wf hwf_env T m (.var x) hdenot
cases hwf_exp with
| wf_var hwf_v => exact hwf_v
```

### 3. extend_cvar Preserves is_implying_wf
For any tvar `X : BVar (s,C) .tvar` in a cvar-extended environment, it must be `.there X'`:
```lean
(env.extend_cvar CS).lookup_tvar (.there X') = env.lookup_tvar X'
```

### 4. EnvTyping for tvar Binding
Structure: `is_proper`, `implies_wf` (derive from `is_proper.2.2.2`), `implies_simple_ans`, `ImplyAfter`, `enforce_pure`

### 5. Explicit Kind Annotations
```lean
cs.rename (Rename.succ (k:=.var))   -- for arrow
cs.rename (Rename.succ (k:=.tvar)) -- for poly
cs.rename (Rename.succ (k:=.cvar)) -- for cpoly
```

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

### SemanticTyping Converts CaptureSet to CapabilitySet
```lean
def SemanticTyping (C : CaptureSet s) (Γ : Ctx s) (e : Exp s) (E : Ty .exi s) : Prop :=
  ∀ ρ m,
    EnvTyping Γ ρ m ->
    Ty.exi_exp_denot ρ E (C.denot ρ m) m (e.subst (Subst.from_TypeEnv ρ))
```

### Body Conditions Use Ground R0
```lean
let R0 := expand_captures m.heap cs'
-- For arrow: R0 ∪ (reachability_of_loc m'.heap arg)
-- For poly/cpoly: just R0
```

## Removed Definitions
These are commented out in Core.lean (no longer needed):
- `Ty.shape_val_denot`, `Ty.capt_val_denot` (replaced by `Ty.val_denot`)
- `Denot.is_reachability_safe/monotonic/tight`
- `TypeEnv.is_reachability_safe/monotonic/tight`

## Tips

1. Use `lean4check` (not `lake build`) for better diagnostics
2. Use `trace_state` to inspect goal context
3. Variables with `✝` suffix are unnamed - use `rename_i` (names from bottom of context)
4. `CapabilitySet` is ground - no need for renaming/substitution in rebind/retype proofs
5. When doing case analysis on `TySort`, only `capt` and `exi` cases exist now
