# Denotation of Capturing Types in Capture Calculus

## Executive Summary

This document explores different design options for the logical interpretation (denotation) of capturing types `S^C` in the Capture Calculus type system. The current denotation effectively erases capture information, treating all types uniformly without leveraging capture constraints. We present seven different semantic approaches and recommend a hybrid solution that extends the existing heap-based semantics with explicit capture indexing.

## Table of Contents

1. [Background and Motivation](#background-and-motivation)
2. [Current State Analysis](#current-state-analysis)
3. [Design Requirements](#design-requirements)
4. [Design Options](#design-options)
5. [Recommendation](#recommendation)
6. [Implementation Strategy](#implementation-strategy)

## Background and Motivation

### The Capture Calculus Type System

The Capture Calculus (CC) introduces capturing types of the form `S^C` where:
- `S` is a shape type (the traditional type structure)
- `C` is a capture set (representing which free variables are captured)

The type system includes:
- **Capture sets**: `C ::= ∅ | {x} | C₁ ∪ C₂ | X` (variables and unions)
- **Capturing types**: `T^C` (shape T with captures C)
- **Capture polymorphism**: `∀C.T` (abstraction over capture sets)
- **Capture existentials**: `∃C.T` (hidden capture witnesses)

### The Problem

The current denotational semantics (`Heap -> Exp {} -> Prop`) doesn't interpret capture sets at all. Captures are essentially erased during semantic translation:

```lean
-- Current approach - no capture interpretation
def Ty.val_denot : TypeEnv s -> Ty .shape s -> Denot
-- Captures in S^C are ignored!
```

This creates a semantic gap: the type system carefully tracks captures, but the semantics doesn't verify or enforce them.

## Current State Analysis

### Existing Semantic Infrastructure

The current denotation uses:

1. **Heap-based semantics**: `Heap := Nat -> Option (Val {})`
2. **Relational denotation**: `Denot := Heap -> Exp {} -> Prop`
3. **Monotonicity**: Denotations preserve under heap extension
4. **Transparency**: Variables reduce to their heap values
5. **Big-step operational semantics**: `Eval : Heap -> Exp {} -> Hpost -> Prop`

### What's Missing

1. **No capture set interpretation**: `S^C` is treated as just `S`
2. **No capture polymorphism semantics**: `∀C.T` lacks semantic treatment
3. **No capture tracking**: Actual runtime captures aren't verified
4. **No capture subsumption**: Can't verify `C₁ ⊆ C₂` semantically

## Design Requirements

A proper semantic treatment of captures must:

### R1: Observable Capture Constraints
- Make capture constraints checkable at runtime
- Verify that actual captures match declared captures

### R2: Compositionality
- Capture denotations must compose properly
- Support capture union: `(S^C₁) ∪ (S^C₂) = S^(C₁∪C₂)`

### R3: Polymorphism Support
- Handle `∀C.T` with proper instantiation
- Support bounded quantification `∀C⊆D.T`

### R4: Operational Correspondence
- Clear connection to big-step evaluation
- Preserve existing evaluation rules

### R5: Monotonicity Preservation
- Maintain heap monotonicity properties
- Support incremental heap extension

### R6: Backwards Compatibility
- Extend rather than replace existing semantics
- Preserve existing proofs where possible

## Design Options

### Option 1: Capture-Indexed Denotations 📍

**Core Idea**: Make denotations explicitly parameterized by capture sets.

```lean
def CaptureAwareDenot := CaptureSet {} -> Heap -> Exp {} -> Prop

def Ty.capt_denot (C : CaptureSet s) (S : Ty .shape s) : CaptureAwareDenot :=
  fun C_actual heap e =>
    C_actual ⊆ C ∧
    ActualCaptures e ⊆ C_actual ∧
    Ty.val_denot S heap e
```

**Pros:**
- ✅ Direct representation of capture constraints
- ✅ Natural capture subsumption via subset relations
- ✅ Clear connection to type system

**Cons:**
- ❌ Need to define runtime capture extraction
- ❌ Composition becomes more complex
- ❌ Capture variables need semantic representation

**Key Insight**: Captures as "ghost state" - they constrain typing without affecting evaluation.

---

### Option 2: Capability-Based Semantics 🔐

**Core Idea**: Model captures as capabilities/permissions required to access values.

```lean
structure Capability where
  variable : Var .var {}
  permission : Permission

def CapabilityDenot := Set Capability -> Heap -> Exp {} -> Prop
```

**Pros:**
- ✅ Natural model for access control
- ✅ Fine-grained permission tracking
- ✅ Connection to effect systems and linear logic

**Cons:**
- ❌ Complex capability propagation
- ❌ Overhead in basic proofs
- ❌ Distant from current infrastructure

**Key Insight**: Captures are "permissions to close over variables" - making the linear/affine connection explicit.

---

### Option 3: Dependency-Tracking Semantics 📊

**Core Idea**: Instrument evaluation to track actual dependencies and verify against declarations.

```lean
structure AccessLog where
  reads : Set Nat
  captures : Set Nat

inductive EvalWithLog : Heap -> Exp {} -> AccessLog -> Exp {} -> Prop

def capt_denot (C : CaptureSet {}) (S : Ty .shape {}) : Denot :=
  fun heap e =>
    ∃ v log,
      EvalWithLog heap e log v ∧
      log.captures ⊆ locations_of C ∧
      S.denot heap v
```

**Pros:**
- ✅ Precise runtime dependency tracking
- ✅ Natural operational correspondence
- ✅ Can detect capture over-approximation

**Cons:**
- ❌ Requires instrumented evaluation
- ❌ Complex for higher-order functions
- ❌ Capture polymorphism handling unclear

**Key Insight**: Use "taint analysis" to monitor value flow.

---

### Option 4: Region/Effect-Based Semantics 🗺️

**Core Idea**: Model captures as effects/regions, similar to region-based memory management.

```lean
structure Region where
  id : Nat
  variables : Set (Var .var {})
  lifetime : Lifetime

def RegionDenot := RegionEnv -> Heap -> Exp {} -> Prop
```

**Pros:**
- ✅ Well-studied theory (region polymorphism)
- ✅ Natural lifetime/scope handling
- ✅ Good for escape analysis

**Cons:**
- ❌ Complex region inference
- ❌ Region hierarchy management
- ❌ Far from current approach

**Key Insight**: Captures are about "escaping scope" - regions make this explicit.

---

### Option 5: Categorical/Monoidal Semantics 🎭

**Core Idea**: Use category theory with captures forming a monoidal structure.

```lean
structure CaptureCategory where
  objects : Type := CaptureSet {}
  morphisms : CaptureSet {} -> CaptureSet {} -> Type
  tensor : CaptureSet {} -> CaptureSet {} -> CaptureSet {}  -- union
  unit : CaptureSet {}  -- empty
```

**Pros:**
- ✅ Elegant mathematical structure
- ✅ Compositionality by construction
- ✅ Natural polymorphism handling

**Cons:**
- ❌ Abstract and complex
- ❌ Hard operational connection
- ❌ Steep learning curve

**Key Insight**: Capture composition (union) has monoidal structure revealing deep regularities.

---

### Option 6: Step-Indexed with Capture Tracking 🔄

**Core Idea**: Extend step-indexing with explicit capture tracking at each step.

```lean
structure IndexedState where
  step : Nat
  heap : Heap
  captured : CaptureSet {}

def StepIndexedCaptDenot := IndexedState -> Exp {} -> Prop
```

**Pros:**
- ✅ Builds on step-indexing infrastructure
- ✅ Clear operational correspondence
- ✅ Natural recursion handling

**Cons:**
- ❌ Complex capture state threading
- ❌ Step management overhead
- ❌ Polymorphism complexity

**Key Insight**: Piggyback capture tracking on existing step-indexing.

---

### Option 7: Game Semantics / Dialog-Based 🎮

**Core Idea**: Model captures as moves in a game between program and environment.

```lean
inductive Move where
  | Question : Var .var {} -> Move  -- "Can I capture x?"
  | Answer : Bool -> Move           -- "Yes/No"
  | Compute : Exp {} -> Move        -- "Evaluate this"
  | Result : Val {} -> Move         -- "Here's the value"
```

**Pros:**
- ✅ Interactive negotiation model
- ✅ Natural for boundaries/interfaces
- ✅ Complex protocol expression

**Cons:**
- ❌ Complex formalization
- ❌ Indirect operational connection
- ❌ Intricate proof obligations

**Key Insight**: Capturing as "negotiation" between function and definition context.

## Recommendation

### Hybrid Approach: Capture-Indexed + Step-Indexed

We recommend combining **Option 1** (Capture-Indexed) with elements of **Option 6** (Step-Indexed) when needed for recursion:

```lean
-- Primary semantic domain with capture awareness
def CaptDenot := CaptureSet {} -> Heap -> Exp {} -> Prop

-- Capturing type interpretation
def Ty.capt_denot (env : TypeEnv s) (C : CaptureSet s) (S : Ty .shape s) : CaptDenot :=
  fun C_actual heap e =>
    -- Soundness: actual captures ⊆ declared captures
    C_actual ⊆ (C.subst env.to_subst) ∧
    -- Shape type satisfaction
    Ty.shape_denot env S heap e ∧
    -- Monotonicity preservation
    ∀ heap' C_actual',
      heap'.subsumes heap ->
      C_actual' ⊆ C_actual ->
      Ty.shape_denot env S heap' e

-- For capture polymorphism
def Ty.cpoly_denot (env : TypeEnv s) (bound : CaptureBound s) (T : Ty .exi (s,C))
  : CaptDenot :=
  fun C_actual heap e =>
    ∃ e0,
      resolve heap e = some (.cabs bound e0) ∧
      ∀ C_inst,
        satisfies_bound C_inst bound ->
        Ty.exi_denot (env.extend_cvar C_inst) T
                     (C_actual ∪ C_inst) heap
                     (e0.subst (Subst.openCVar C_inst))

-- For existential captures
def Ty.exi_capt_denot (env : TypeEnv s) (T : Ty .capt (s,C)) : CaptDenot :=
  fun C_actual heap e =>
    ∃ C_witness,
      Ty.capt_denot (env.extend_cvar C_witness) T C_actual heap e
```

### Why This Approach?

1. **Minimal Extension**: Builds naturally on existing `Denot` infrastructure
2. **Direct Representation**: Capture constraints are first-class
3. **Compositional**: Capture union naturally composes
4. **Operational Correspondence**: Clear connection to evaluation
5. **Polymorphism-Friendly**: Natural handling of `∀C.T` and `∃C.T`
6. **Monotonicity Preserved**: Maintains heap monotonicity properties
7. **Incremental Implementation**: Can be added gradually

### Key Design Decisions

#### Capture Extraction

Define a function to extract actual captures from runtime values:

```lean
def ActualCaptures : Exp {} -> CaptureSet {}
| .var x => {x}
| .abs T e => ActualCaptures e \ {x}  -- remove bound variable
| .app f x => ActualCaptures f ∪ ActualCaptures x
-- ... etc
```

#### Capture Variables in Environment

Extend `TypeInfo` to include capture denotations:

```lean
inductive TypeInfo : Kind -> Type where
| var : Nat -> TypeInfo .var
| tvar : Denot -> TypeInfo .tvar
| cvar : CaptureSet {} -> TypeInfo .cvar  -- NEW: capture instantiation
```

#### Semantic Typing Update

```lean
def SemanticTyping (Γ : Ctx s) (C : CaptureSet s) (e : Exp s) (T : Ty .exi s) : Prop :=
  ∀ env store C_actual,
    EnvTyping Γ env store ->
    C_actual ⊆ (C.subst (Subst.from_TypeEnv env)) ->
    Ty.exi_denot env T C_actual store (e.subst (Subst.from_TypeEnv env))

notation:65 C " # " Γ " ⊨ " e " : " T => SemanticTyping Γ C e T
```

## Implementation Strategy

### Phase 1: Core Infrastructure (Week 1-2)
1. Define `CaptDenot` type
2. Implement `ActualCaptures` extraction
3. Prove basic properties (monotonicity, composition)
4. Extend `TypeInfo` with capture variables

### Phase 2: Type Denotations (Week 2-3)
1. Implement `Ty.capt_denot` for capturing types
2. Implement `Ty.cpoly_denot` for capture polymorphism
3. Implement `Ty.exi_capt_denot` for existentials
4. Prove denotation properties (rebinding, retyping)

### Phase 3: Semantic Typing (Week 3-4)
1. Update `SemanticTyping` with capture parameter
2. Update `EnvTyping` for capture variables
3. Prove environment properties
4. Connect to operational semantics

### Phase 4: Soundness Proof (Week 4-6)
1. Prove fundamental lemma (syntactic typing implies semantic)
2. Prove progress and preservation with captures
3. Prove capture safety (no capture violations at runtime)
4. Complete end-to-end soundness theorem

### Testing Strategy

Create test cases for:
1. Simple capture propagation
2. Capture polymorphism instantiation
3. Existential packing/unpacking
4. Nested captures
5. Capture subsumption

### Migration Path

1. Keep existing `Denot` as special case where `C = ∅`
2. Gradually port existing proofs to use `CaptDenot`
3. Maintain backwards compatibility layer
4. Eventually deprecate capture-unaware denotations

## Conclusion

The recommended hybrid approach provides a principled semantic foundation for capturing types while maintaining the elegance of the existing framework. By making captures first-class in the denotation, we can verify capture safety and support advanced features like capture polymorphism, all while preserving the operational correspondence and compositional structure of the current semantics.

This design balances theoretical elegance with practical implementability, providing a clear path forward for the Capture Calculus soundness proof.