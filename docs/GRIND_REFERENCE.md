# Lean 4 `grind` Tactic Comprehensive Reference

**For LLM Coding Agents**

This document provides a comprehensive reference for using the `grind` tactic in Lean 4, compiled from the official Lean documentation.

---

## Table of Contents

1. [Overview](#overview)
2. [Basic Usage](#basic-usage)
3. [Core Mechanisms](#core-mechanisms)
4. [Attributes](#attributes)
5. [Configuration Options](#configuration-options)
6. [Specialized Solvers](#specialized-solvers)
7. [Tactic Variants](#tactic-variants)
8. [Best Practices](#best-practices)
9. [Examples](#examples)
10. [Limitations](#limitations)

---

## Overview

### What is `grind`?

The `grind` tactic is an automated proof construction tool inspired by modern SMT (Satisfiability Modulo Theories) solvers. It uses multiple cooperating engines to automatically construct proofs by incrementally collecting and deriving facts.

### Key Characteristics

- **Proof by Contradiction**: All `grind` proofs work by attempting to derive a contradiction
- **Virtual Whiteboard**: Facts are discovered, tracked, and shared among reasoning engines
- **Equivalence Classes**: Tracks propositions known to be true/false and terms known to be equal
- **Standard Lean Proofs**: Produces standard Lean proof terms, not external certificates
- **Automatic Lemma Discovery**: Automatically discovers and uses theorems annotated with `@[grind]`

### Cooperating Engines

1. **Congruence Closure**: Discovers and tracks sets of equal terms
2. **Constraint Propagation**: Derives new facts from existing constraints
3. **E-matching**: Heuristically instantiates theorems by pattern matching
4. **Guided Case Analysis**: Performs strategic case splitting
5. **Theory Solvers**:
   - Linear integer arithmetic (`cutsat`)
   - Commutative rings and fields (algebraic solver / "ring")
   - Linear arithmetic for modules and rings

---

## Basic Usage

### Syntax Variants

```lean
-- Basic usage: uses @[grind] tagged theorems
grind

-- With additional theorems
grind [theorem1, theorem2, ...]

-- Only specified theorems (excludes @[grind] tagged ones)
grind only [theorem1, theorem2, ...]

-- With configuration parameters
grind (config := { option := value })
grind (gen := 20) (ematch := 10) (splits := 5)

-- With feature flags
grind +option    -- Enable a feature
grind -option    -- Disable a feature
```

### Simple Examples

```lean
-- Equality transitivity
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by grind

-- With explicit theorems
example : some_goal := by grind [my_lemma, my_theorem]
```

---

## Core Mechanisms

### Congruence Closure

Congruence closure discovers sets of equal terms by:
- Tracking equivalence classes of terms
- Merging buckets of equal terms
- Automatically proving transitivity and substitution

**Example:**
```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by grind
```

### Constraint Propagation

Derives new facts from existing constraints by:
- Propagating logical facts through the context
- Combining constraints to derive contradictions
- Working with the virtual whiteboard of shared facts

### E-matching

E-matching is heuristic theorem instantiation by pattern matching. It finds matches for theorem patterns while accounting for known equalities.

#### E-matching Attributes

- **`@[grind =]`**: Uses the left-hand side of an equality as a pattern
  ```lean
  @[grind =] theorem gf (x : Nat) : g (f x) = x := by simp [f, g]
  ```

- **`@[grind →]`**: Forward reasoning - selects multi-pattern from hypotheses
  ```lean
  @[grind →] theorem forward_thm (h : P x) : Q x := ...
  ```

- **`@[grind ←]`**: Backward reasoning - selects multi-pattern from conclusion
  ```lean
  @[grind ←] theorem backward_thm : P x → Q x := ...
  ```

#### Pattern Matching Details

- E-matching finds matches modulo equalities discovered by congruence closure
- Can instantiate theorems even when patterns don't match syntactically
- Generation limits prevent infinite instantiation chains
- Multi-patterns require multiple conditions to match simultaneously

### Case Analysis

Guided case analysis performs strategic case splitting:
- Splits on inductive types and predicates
- Uses `@[grind_cases]` attribute to mark splittable types
- Respects `splits` configuration to limit search depth
- Can split on `match`, `if-then-else`, and inductive predicates (configurable)

---

## Attributes

### `@[grind]`

Marks theorems for automatic discovery and use by `grind`.

```lean
@[grind]
theorem my_useful_lemma : ... := ...
```

### `@[grind =]`, `@[grind →]`, `@[grind ←]`

Control E-matching pattern selection:

- **`@[grind =]`**: Uses LHS of equality as pattern
- **`@[grind →]`**: Forward reasoning from hypotheses
- **`@[grind ←]`**: Backward reasoning from conclusion

```lean
@[grind =] theorem my_eq : f (g x) = x := ...
@[grind →] theorem my_fwd : P → Q := ...
@[grind ←] theorem my_bwd : P → Q := ...
```

### `@[grind_cases]`

Marks inductive types/predicates for case splitting during search.

```lean
@[grind_cases]
inductive MyType where
  | constructor1
  | constructor2
```

**Eager variant**: `@[grind_cases eager]` enables case splitting during preprocessing.

### `@[grind_norm]` and `@[grind_norm_proc]`

Marks normalization theorems and procedures for expression preprocessing.

```lean
@[grind_norm]
theorem my_simp_rule : complicated_expr = simplified_expr := ...
```

---

## Configuration Options

### Numeric Parameters

Control search depth and instantiation:

```lean
-- Maximum term generation depth (default varies)
grind (gen := 20)

-- Maximum E-matching rounds before each case split
grind (ematch := 10)

-- Maximum search tree depth (case splits)
grind (splits := 5)
```

**Generation Explanation:**
- Input goal terms have generation 0
- When a theorem is instantiated with generation-n terms, resulting terms are generation n+1
- Limits length of instantiation chains to prevent infinite loops

### Boolean Configuration Flags

#### Split Control

```lean
-- Enable/disable splitting on implications
grind +splitImp   -- Enable splitting on A → B when A is propositional
grind -splitImp   -- Disable (default varies)

-- Control match expression splitting
grind +splitMatch  -- Enable case-splitting on match during search
grind -splitMatch  -- Disable

-- Control if-then-else splitting
grind +splitIte    -- Enable case-splitting on if-then-else
grind -splitIte    -- Disable

-- Control inductive predicate splitting
grind +splitIndPred  -- Split on all inductive predicates
grind -splitIndPred  -- Only split on @[grind_cases] marked types
```

#### Solver Control

```lean
-- Disable linear arithmetic solver for modules/rings
grind -linarith

-- Disable cutsat solver (for debugging)
grind -cutsat

-- Accept rational models in linear integer arithmetic
-- (shrinks search space but incomplete for ℤ)
grind +qlia

-- Use all [ext] theorems in environment
grind +extAll

-- Disable match equation generation
grind -matchEqs
```

#### Diagnostic Control

```lean
-- Enable tracing of E-matching theorems and case-splits
grind (config := { trace := true })

-- Disable all diagnostics (used by try?)
grind -verbose
```

### Combined Configuration

```lean
grind (gen := 20) (ematch := 15) (splits := 8) +splitImp -linarith
```

---

## Specialized Solvers

### Linear Integer Arithmetic (LIA) - `cutsat`

Solves goals reducible to linear integer arithmetic using the `cutsat` decision procedure.

**Capabilities:**
- Handles linear inequality systems over integers
- Performs case analysis on integer variables
- Detects contradictions in constraint sets
- Complete decision procedure for LIA

**Example:**
```lean
example (x y : Int) :
  27 ≤ 11 * x + 13 * y →
  11 * x + 13 * y ≤ 45 →
  -10 ≤ 7 * x - 9 * y →
  7 * x - 9 * y ≤ 4 →
  False := by grind
```

**Configuration:**
```lean
grind -cutsat    -- Disable the cutsat solver
grind +qlia      -- Accept rational models (incomplete but faster)
```

### Algebraic Solver (Commutative Rings/Fields)

Solves polynomial equations and disequations over commutative rings, semirings, and fields using Gröbner basis techniques.

**Requirements:**
- Type classes: `CommRing`, `NoNatZeroDivisors`, `Field`, etc.
- Works with polynomial equations

**Example:**
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b c : α) :
  a + b + c = 3 →
  a^2 + b^2 + c^2 = 5 →
  a^3 + b^3 + c^3 = 7 →
  a^4 + b^4 = 9 - c^4 := by grind
```

**Finite Field Example:**
```lean
example (x y : Fin 11) :
  x^2 * y = 1 →
  x * y^2 = y →
  y * x = 1 := by grind
```

### Linear Arithmetic Solver

Separate from LIA, handles linear arithmetic over ordered modules and rings.

**Configuration:**
```lean
grind -linarith   -- Disable this solver
```

---

## Tactic Variants

### `grind?`

Diagnostic variant that traces used theorems and case splits, then reports an equivalent minimal `grind only` call.

**Usage:**
```lean
example : some_goal := by grind?
-- Output: Try this: grind only [theorem1, theorem3]
```

**Purpose:**
- Reduce noise in proofs
- Understand what `grind` actually used
- Create minimal reproducible proofs
- Help with proof maintenance

**Note:** Set `trace := true` in configuration to enable detailed tracing:
```lean
grind (config := { trace := true })
```

### `cutsat`

Specialized wrapper around `grind` focused exclusively on linear integer arithmetic.

**Usage:**
```lean
example (x y : Int) : 2 * x + 4 * y ≠ 5 := by cutsat
```

**When to use:** When your goal is purely a LIA problem without needing other solvers.

### `grobner`

Specialized wrapper around `grind` for polynomial equation solving using Gröbner basis.

**Usage:**
```lean
example [CommRing α] : some_polynomial_goal := by grobner
```

**When to use:** For goals that are purely algebraic equations over rings/fields.

---

## Best Practices

### When to Use `grind`

✅ **Good Use Cases:**
- Equality reasoning (transitivity, substitution)
- Algebraic equations and identities
- Linear integer arithmetic problems
- Finite field arithmetic
- Goals with relatively small search spaces
- Problems solvable through congruence closure

❌ **Poor Use Cases:**
- Massive combinatorial search spaces
- Pigeonhole principle instances
- Graph coloring problems
- High-order N-queens
- Large Sudoku encodings
- Bit-level Boolean combinatorics

### Alternative Tactics

For complex combinatorial Boolean problems, use `bv_decide`:
```lean
example : complex_boolean_goal := by bv_decide
```

**Why `bv_decide` for combinatorics:**
- Calls state-of-the-art external SAT solver
- Performs heavy search outside Lean
- Returns compact machine-checkable certificate
- Verifies certificate inside Lean

### Debugging Failed `grind` Proofs

1. **Use `grind?`** to see what theorems were attempted
2. **Increase limits:**
   ```lean
   grind (gen := 50) (ematch := 50) (splits := 20)
   ```
3. **Enable tracing:**
   ```lean
   grind (config := { trace := true })
   ```
4. **Try adding relevant theorems explicitly:**
   ```lean
   grind [lemma1, lemma2, lemma3]
   ```
5. **Check if a specialized solver is needed:**
   ```lean
   grind +splitImp    -- Enable implication splitting
   grind +extAll      -- Use all extensionality theorems
   ```
6. **Disable problematic solvers:**
   ```lean
   grind -cutsat      -- If LIA solver causes issues
   grind -linarith    -- If linear arithmetic solver causes issues
   ```

### Performance Tips

1. **Start with `grind`** - it's often sufficient
2. **Use `grind only [...]`** for faster, more predictable proofs
3. **Add specific theorems** when automatic discovery isn't working
4. **Set reasonable limits** on generation and ematch rounds
5. **Use specialized wrappers** (`cutsat`, `grobner`) when applicable

---

## Examples

### Congruence Closure Examples

```lean
-- Simple transitivity
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by grind

-- Function congruence
example (f : Nat → Nat) (a b : Nat) (h : a = b) : f a = f b := by grind
```

### Algebraic Reasoning

```lean
-- Commutative ring
example [CommRing α] [NoNatZeroDivisors α] (a b c : α) :
  a + b + c = 3 →
  a^2 + b^2 + c^2 = 5 →
  a^3 + b^3 + c^3 = 7 →
  a^4 + b^4 = 9 - c^4 := by grind

-- Finite fields
example (x y : Fin 11) :
  x^2 * y = 1 →
  x * y^2 = y →
  y * x = 1 := by grind
```

### Linear Integer Arithmetic

```lean
-- Impossibility proof
example (x y : Int) :
  27 ≤ 11 * x + 13 * y →
  11 * x + 13 * y ≤ 45 →
  -10 ≤ 7 * x - 9 * y →
  7 * x - 9 * y ≤ 4 →
  False := by grind

-- Simple disequality
example (x y : Int) : 2 * x + 4 * y ≠ 5 := by cutsat
```

### E-matching with Custom Theorems

```lean
def f (a : Nat) : Nat := a + 1
def g (a : Nat) : Nat := a - 1

-- Mark theorem for E-matching
@[grind =] theorem gf (x : Nat) : g (f x) = x := by simp [f, g]

-- Now grind can use this automatically
example (n : Nat) : g (f n) = n := by grind
```

### Forward Reasoning

```lean
-- Forward reasoning from hypothesis
@[grind →] theorem my_forward : P x → Q x → R x := ...

example (hp : P a) (hq : Q a) : R a := by grind
```

### Backward Reasoning

```lean
-- Backward reasoning from conclusion
@[grind ←] theorem my_backward : P x → Q x := ...

example : P a → Q a := by grind
```

### Configuration Examples

```lean
-- Increased limits for harder problem
example : hard_goal := by
  grind (gen := 30) (ematch := 25) (splits := 10)

-- With specific features
example : goal_with_implications := by
  grind (gen := 20) +splitImp +extAll

-- Minimal solver set
example : simple_goal := by
  grind only [needed_lemma] -cutsat -linarith
```

### Case Splitting

```lean
-- Define type with case splitting
@[grind_cases]
inductive Color where
  | Red
  | Blue
  | Green

-- grind will automatically case split on Color
example (c : Color) :
  c = Color.Red ∨ c = Color.Blue ∨ c = Color.Green := by grind
```

---

## Limitations

### What `grind` Is Not Designed For

1. **Exponential Search Spaces**
   - Pigeonhole principle
   - Graph coloring
   - N-queens (large N)
   - Sudoku (large grids)

2. **Pure Boolean SAT Problems**
   - Use `bv_decide` instead
   - `grind` is not optimized for massive case analysis

3. **Highly Non-linear Problems**
   - Very complex algebraic constraints
   - Higher-order logic puzzles

### Common Failure Modes

1. **Timeout**: Search space too large
   - Solution: Increase limits or use more specific theorems

2. **Missing Lemmas**: Required theorem not discovered
   - Solution: Add explicitly with `grind [lemma]`

3. **Wrong Solver**: Problem needs different approach
   - Solution: Try `bv_decide`, `omega`, `ring`, etc.

4. **Infinite Instantiation**: E-matching creates unbounded terms
   - Solution: Lower `gen` limit or disable problematic patterns

### Error Messages

When `grind` fails, it may produce errors such as:
- `tactic 'grind' failed` - Could not find proof
- Timeout errors - Search space too large
- Specific solver errors - Check solver configuration

**Debugging approach:**
1. Use `grind?` to see what's happening
2. Check trace output with `trace := true`
3. Try simplified version of goal
4. Add relevant lemmas explicitly
5. Adjust configuration parameters

---

## Preprocessing

### Normalization

`grind` performs normalization before search:
- Unfolds local definitions (configurable)
- Performs zeta reduction (let-expression substitution)
- Applies `@[grind_norm]` theorems
- Canonicalizes types and instances

### Universe-Level Normalization

Preprocessing includes universe-level normalization to avoid missing equalities in congruence closure.

### Injection and Cases Handling

The preprocessor introduces:
- Local declarations for minor premises
- Case analysis for `@[grind_cases eager]` marked types
- Propositions for each constructor

---

## Additional Resources

- **Official Documentation**: [https://lean-lang.org/doc/reference/latest/The--grind--tactic/](https://lean-lang.org/doc/reference/latest/The--grind--tactic/)
- **Mathlib4 Documentation**: [https://leanprover-community.github.io/mathlib4_docs/Init/Grind/Tactics.html](https://leanprover-community.github.io/mathlib4_docs/Init/Grind/Tactics.html)
- **Tactic Reference**: [https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/)

---

## Quick Reference Card

### Common Patterns

```lean
-- Basic proof
by grind

-- With explicit lemmas
by grind [lemma1, lemma2]

-- Only specific lemmas (no @[grind] tagged)
by grind only [lemma1, lemma2]

-- With configuration
by grind (gen := 20) (ematch := 10)

-- Enable/disable features
by grind +splitImp -cutsat

-- Diagnostic version
by grind?

-- Specialized solvers
by cutsat     -- Linear integer arithmetic only
by grobner    -- Polynomial equations only
```

### Attribute Quick Reference

```lean
@[grind]              -- Auto-discovered by grind
@[grind =]            -- E-match on LHS of equality
@[grind →]            -- Forward reasoning
@[grind ←]            -- Backward reasoning
@[grind_cases]        -- Case split during search
@[grind_cases eager]  -- Case split during preprocessing
@[grind_norm]         -- Normalization theorem
```

### Configuration Quick Reference

```lean
-- Numeric limits
(gen := n)      -- Term generation depth
(ematch := n)   -- E-matching rounds
(splits := n)   -- Search tree depth

-- Boolean flags (prefix with + or -)
splitImp        -- Split on implications
splitMatch      -- Split on match expressions
splitIte        -- Split on if-then-else
splitIndPred    -- Split on inductive predicates
cutsat          -- Linear integer arithmetic solver
linarith        -- Linear arithmetic solver
qlia            -- Accept rational models in LIA
extAll          -- Use all extensionality theorems
matchEqs        -- Generate match equations
verbose         -- Diagnostic output
```

---

## Conclusion

The `grind` tactic is a powerful automated reasoning tool for Lean 4 that combines multiple solving techniques. It excels at:
- Equality reasoning
- Algebraic problems
- Linear arithmetic
- Problems with modest search spaces

For best results:
- Start simple with `grind`
- Add explicit theorems when needed
- Use specialized variants for specific problem types
- Switch to `bv_decide` for large combinatorial problems
- Use `grind?` to understand and minimize proofs

Remember: `grind` produces standard Lean proof terms, so all proofs are fully verified by Lean's kernel.
