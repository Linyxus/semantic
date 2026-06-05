import Semantic.Consume.Debruijn

import Semantic.Consume.Syntax

import Semantic.Consume.Substitution

import Semantic.Consume.TypeSystem

import Semantic.Consume.Semantics

import Semantic.Consume.Denotation

import Semantic.Consume.Fundamental

import Semantic.Consume.Safety

/-!
# Semantic Type Soundness for Consume

This module develops semantic type soundness of System Consume. It is another
intermediate step towards System Capybara.

`Semantic.Consume.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.Consume.Debruijn`.
Then, `Semantic.Consume.Substitution` establishes substitution operations and
properties for the syntax.
On top of that, `Semantic.Consume.TypeSystem` and `Semantic.Consume.Semantics`
define the type system and the reduction semantics respectively.

Then, the `Semantic.Consume.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types are logical
predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates, and proves
properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.Consume.Fundamental` and `Semantic.Consume.Safety`
establishes semantic type soundness of Capture Calculus.
It proves the fundamental theorem: syntactic typing (which is defined in
`Semantic.Consume.TypeSystem`) implies semantic typing.
Then, it proves safety: well-typed programs are always progressive.

This is considered an intermediate step towards the "actual" Capybara.
-/
