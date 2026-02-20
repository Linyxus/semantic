# Semantic Type Soundness for System Capless

This repo mechanises semantic type soundness for System Capless in Lean 4.

## Build

```
lake exe cache get
lake build
```

## Project Structure

- `Semantic/CC/Syntax/` — Syntax definitions
- `Semantic/CC/TypeSystem/` — Typing rules
- `Semantic/CC/Semantics/` — Operational semantics
- `Semantic/CC/Substitution.lean` — Substitution lemmas
- `Semantic/CC/Denotation/` — Semantic interpretation of types
- `Semantic/CC/Fundamental.lean` — Fundamental theorem
- `Semantic/CC/Safety.lean` — Type safety
