import Semantic.CCPrec.Debruijn

import Semantic.CCPrec.Syntax

import Semantic.CCPrec.Substitution

import Semantic.CCPrec.TypeSystem

import Semantic.CCPrec.Semantics

import Semantic.CCPrec.Denotation

import Semantic.CCPrec.Fundamental

import Semantic.CCPrec.Safety

/-!
# Semantic Type Soundness for Capture Calculus with Precise Capabilities

This module develops semantic type soundness of System Capless with precise capabilities.

`Semantic.CCPrec.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.CCPrec.Debruijn`.
Then, `Semantic.CCPrec.Substitution` establishes substitution operations and properties
for the syntax.
On top of that, `Semantic.CCPrec.TypeSystem` and `Semantic.CCPrec.Semantics` defines
the type system and the reduction semantics respectively.

Then, the `Semantic.CCPrec.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types are logical
predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates, and proves
properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.CCPrec.Fundamental` and `Semantic.CCPrec.Safety` establishes
semantic type soundness of Capture Calculus with Precise Capabilities.
It proves the fundamental theorem: syntactic typing
(which is defined in `Semantic.CCPrec.TypeSystem`) implies semantic typing.
Then, it proves safety: well-typed programs are always progressive.
-/
