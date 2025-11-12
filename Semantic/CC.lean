import Semantic.CC.Debruijn

import Semantic.CC.Syntax

import Semantic.CC.Substitution

import Semantic.CC.TypeSystem

import Semantic.CC.Semantics

import Semantic.CC.Denotation

import Semantic.CC.Soundness

import Semantic.CC.CapturePrediction

/-!
# Semantic Type Soundness for Capture Calculus

This module develops semantic type soundness of System Capless.

`Semantic.CC.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.CC.Debruijn`.
Then, `Semantic.CC.Substitution` establishes substitution operations and properties for the syntax.
On top of that, `Semantic.CC.TypeSystem` and `Semantic.CC.Semantics` defines the type system and
the reduction semantics respectively.

Then, the `Semantic.CC.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types are logical
predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates, and proves
properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.CC.Soundness` establishes semantic type soundness of Capture Calculus.
It proves the fundamental theorem: syntactic typing (which is defined in `Semantic.CC.TypeSystem`)
implies semantic typing.
-/
