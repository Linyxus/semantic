import Semantic.CoreCapybara.Debruijn

import Semantic.CoreCapybara.Syntax

import Semantic.CoreCapybara.Substitution

import Semantic.CoreCapybara.TypeSystem

import Semantic.CoreCapybara.Semantics

import Semantic.CoreCapybara.Denotation

import Semantic.CoreCapybara.Fundamental

import Semantic.CoreCapybara.Gaps

import Semantic.CoreCapybara.Safety

import Semantic.CoreCapybara.Semantics.Standardization

/-!
# Semantic Type Soundness for CoreCapybara

This module develops semantic type soundness of System CoreCapybara.
It is based on System Capybara.

`Semantic.CoreCapybara.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.CoreCapybara.Debruijn`.
Then, `Semantic.CoreCapybara.Substitution` establishes substitution operations and
properties for the syntax.
On top of that, `Semantic.CoreCapybara.TypeSystem` and `Semantic.CoreCapybara.Semantics`
define the type system and the reduction semantics respectively.

Then, the `Semantic.CoreCapybara.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types are logical
predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates, and proves
properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.CoreCapybara.Fundamental` and `Semantic.CoreCapybara.Safety`
establishes semantic type soundness of Capture Calculus.
It proves the fundamental theorem: syntactic typing (which is defined in
`Semantic.CoreCapybara.TypeSystem`) implies semantic typing.
Then, it proves safety: well-typed programs are always progressive.

This is considered an intermediate step towards the "actual" Capybara.
-/
