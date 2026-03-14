import Semantic.CCPath.Debruijn

import Semantic.CCPath.Syntax

import Semantic.CCPath.Substitution

import Semantic.CCPath.TypeSystem

import Semantic.CCPath.Semantics

import Semantic.CCPath.Denotation

import Semantic.CCPath.Fundamental

import Semantic.CCPath.Safety

/-!
# Semantic Type Soundness for Capture Calculus

This module develops semantic type soundness of System Capless.

`Semantic.CCPath.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.CCPath.Debruijn`.
Then, `Semantic.CCPath.Substitution` establishes substitution operations and properties for the syntax.
On top of that, `Semantic.CCPath.TypeSystem` and `Semantic.CCPath.Semantics` defines the type system and
the reduction semantics respectively.

Then, the `Semantic.CCPath.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types are logical
predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates, and proves
properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.CCPath.Fundamental` and `Semantic.CCPath.Safety` establishes
semantic type soundness of Capture Calculus.
It proves the fundamental theorem: syntactic typing (which is defined in `Semantic.CCPath.TypeSystem`)
implies semantic typing.
Then, it proves safety: well-typed programs are always progressive.
-/
