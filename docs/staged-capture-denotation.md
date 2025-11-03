# Refactor: Single Source of Truth for Capture Variable Denotation

## Problem

Currently `TypeEnv.extend_cvar` stores both:
- A capture set `cs : CaptureSet {}`
- Its denotation `c : CapDenot`

This creates redundancy and complicates well-formedness tracking in proofs (`Retype`, `Rebind`).

## Solution

Store only the capture set `cs : CaptureSet {}`. Compute denotation on-demand via `cs.denot TypeEnv.empty`.

## Key Changes

1. **TypeEnv**: `extend_cvar cs c` → `extend_cvar cs`
2. **EnvTyping.cvar**: Remove conjunct `cs.denot TypeEnv.empty = denot`
3. **Lookups**: `(env.lookup_cvar C).2` → `(env.lookup_cvar C).denot TypeEnv.empty`
4. **Rebind/Retype**: `cvar` fields relate capture sets syntactically/semantically

## Benefits

- Single source of truth eliminates inconsistency
- Simpler well-formedness preservation proofs
- More principled: denotation always derived from capture set
