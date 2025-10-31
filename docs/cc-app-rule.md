# Application Rule Soundness Issue

## Problem

After commit "CC: tighten the denotation of functions" (bc82a95), the `sem_typ_app` soundness proof cannot be completed due to a capability set mismatch.

## Root Cause

The arrow denotation now uses runtime reachability:
```lean
T2 (A ∪ (reachability_of_loc m' arg)) m' ...
```

But the typing and evaluation rules require matching capability sets:
```lean
-- Typing rule
HasType C Γ (.var x) (.typ (.capt Cx (.arrow T1 T2)))
HasType C Γ (.var y) (.typ T1)
---------------------------------------------------
HasType C Γ (.app x y) (T2.subst (Subst.openVar y))

-- Eval rule
Eval C m (body) Q → Eval C m (.app x y) Q
```

**The mismatch**: Denotation gives us `Eval (Cx ∪ reachability_of_loc ...) ...` but typing requires `Eval C ...`.

## Why No Fix Exists

1. **No Eval weakening**: Cannot prove `Eval A ... → Eval B ...` because `C` controls which capabilities can be invoked (`eval_invoke` checks `x ∈ C`)
2. **No derivable relationship**: Cannot derive `C = Cx ∪ reachability_of_loc` from typing assumptions alone

## Solutions

### Option 1: Add Capability Constraint (Recommended)
Modify the typing rule to make capability tracking explicit:
```lean
| app :
  HasType C Γ (.var x) (.typ (.capt Cx (.arrow T1 T2))) ->
  HasType C Γ (.var y) (.typ T1) ->
  Subcapt Γ (Cx ∪ captures_of(y)) C ->  -- NEW
  ----------------------------
  HasType C Γ (.app x y) (T2.subst (Subst.openVar y))
```

**Pros**: Principled; reveals necessary type system constraint
**Cons**: Requires updating all typing derivations

### Option 2: Modify Evaluation Rule
Change `eval_apply` to extend capability sets:
```lean
| eval_apply {m : Memory} {x : Nat} :
  m.lookup x = some (.val ⟨.abs cs T e, hv, R⟩) ->
  m.lookup y = some (.val ⟨v, hv', R'⟩) ->
  Eval (C ∪ R ∪ R') m (e.subst (Subst.openVar y)) Q ->
  ------------------------------------------------
  Eval C m (.app (.free x) y) Q
```

**Pros**: Matches denotation semantics
**Cons**: Changes operational semantics; more complex

### Option 3: Revert Denotation Change
Undo commit bc82a95 and use `T1.captureSet.denot env` instead of `reachability_of_loc`.

**Pros**: Immediate compatibility
**Cons**: Loses semantic precision

## Current Status

- **Problem 1** (opening lemma): Solvable with specialized `Retype` relation
- **Problem 2** (capability mismatch): Blocks proof completion

A conditional proof is possible assuming capability set equality.
