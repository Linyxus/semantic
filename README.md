# Semantic Type Soundness in Lean 4

This repo practices semantic type soundness for various calculi.

## Setup

This project makes extensive use of Claude for proof writing.
See [CLAUDE.md](./CLAUDE.md) for the project-level instructions.
It assumes a MCP tool called `lean4check`, which can be found in [this project](https://github.com/linyxus/ucw).

To setup MCP, clone the aforementioned `ucw` repo somewhere on your machine. Then, go back to the root of this project, and run:
```
claude mcp add lean4check -- uv --project <UCW_ROOT>/lean4check run lean4check --root <THIS_PROJECT_ROOT>
```

This tiny MCP server provides only one tool `check`, which compiles a Lean 4 module and output all diagnostics with its context. Less is more!

## Simply Typed Lambda Calculus

- [BigStep](Semantic/Stlc/BigStep/Soundness.lean) proves semantic type soundness for STLC with big-step operational semantics.
- [SmallStep](Semantic/Stlc/SmallStep/Soundness.lean) proves semantic type soundness for STLC with small-step operational semantics.
  Interestingly, the definitions and proofs are mostly done by an LLM with the big-step version as reference.

## MNF System F<: with Singleton Types

The module [Fsub](Semantic/Fsub.lean) includes a semantic type soundness formulation of System F<: in monadic normal forms with singleton types (types like `x.type`).

## System Capless

The module [CC](Semantic/CC.lean) mechanises semantic type soundness for System Capless.

