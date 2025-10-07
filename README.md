# Semantic Type Soundness in Lean 4

This repo practices semantic type soundness for various calculi.

## Simply Typed Lambda Calculus

- [BigStep](Semantic/Stlc/BigStep/Soundness.lean) proves semantic type soundness for STLC with big-step operational semantics.
- [SmallStep](Semantic/Stlc/SmallStep/Soundness.lean) proves semantic type soundness for STLC with small-step operational semantics.
  Interestingly, the definitions and proofs are mostly done by an LLM with the big-step version as reference.

## MNF System F<: with Singleton Types

The module [Fsub](Semantic/Fsub.lean) includes a semantic type soundness formulation of System F<: in monadic normal forms with singleton types (types like `x.type`).

