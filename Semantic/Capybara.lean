import Semantic.Capybara.Debruijn

import Semantic.Capybara.Syntax

import Semantic.Capybara.Substitution

import Semantic.Capybara.TypeSystem

import Semantic.Capybara.Semantics

import Semantic.Capybara.Denotation

-- WIP
--import Semantic.Capybara.Fundamental
--import Semantic.Capybara.Safety

/-!
# Semantic Type Soundness for Capybara

This module develops semantic type soundness of System Capybara. It is based on System Capless.

`Semantic.Capybara.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.Capybara.Debruijn`.
Then, `Semantic.Capybara.Substitution` establishes substitution operations and
properties for the syntax.
On top of that, `Semantic.Capybara.TypeSystem` and `Semantic.Capybara.Semantics`
define the type system and the reduction semantics respectively.

Then, the `Semantic.Capybara.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types are logical
predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates, and proves
properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.Capybara.Fundamental` and `Semantic.Capybara.Safety`
establishes semantic type soundness of Capture Calculus.
It proves the fundamental theorem: syntactic typing (which is defined in
`Semantic.Capybara.TypeSystem`) implies semantic typing.
Then, it proves safety: well-typed programs are always progressive.
-/
