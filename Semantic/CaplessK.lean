import Semantic.CaplessK.Debruijn

import Semantic.CaplessK.Syntax

import Semantic.CaplessK.Substitution

import Semantic.CaplessK.TypeSystem

import Semantic.CaplessK.Semantics

import Semantic.CaplessK.Denotation

import Semantic.CaplessK.Fundamental

import Semantic.CaplessK.Safety

/-!
# Semantic Type Soundness for CaplessK

This module develops semantic type soundness of System CaplessK.

`Semantic.CaplessK.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.CaplessK.Debruijn`.
Then, `Semantic.CaplessK.Substitution` establishes substitution operations and
properties for the syntax.
On top of that, `Semantic.CaplessK.TypeSystem` and `Semantic.CaplessK.Semantics`
defines the type system and the reduction semantics respectively.

Then, the `Semantic.CaplessK.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types
are logical predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates,
and proves properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.CaplessK.Fundamental` and `Semantic.CaplessK.Safety`
establishes semantic type soundness of CaplessK.
It proves the fundamental theorem: syntactic typing
(which is defined in `Semantic.CaplessK.TypeSystem`) implies semantic typing.
Then, it proves safety: well-typed programs are always progressive.
-/
