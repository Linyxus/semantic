import Semantic.ModalCapybara.Debruijn

import Semantic.ModalCapybara.Syntax

import Semantic.ModalCapybara.Substitution

import Semantic.ModalCapybara.TypeSystem

import Semantic.ModalCapybara.Semantics

import Semantic.ModalCapybara.Denotation

import Semantic.ModalCapybara.Fundamental

import Semantic.ModalCapybara.Safety

/-!
# Semantic Type Soundness for ModalCapybara

This module develops semantic type soundness of System ModalCapybara.
It is based on System Capybara.

`Semantic.ModalCapybara.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.ModalCapybara.Debruijn`.
Then, `Semantic.ModalCapybara.Substitution` establishes substitution operations and
properties for the syntax.
On top of that, `Semantic.ModalCapybara.TypeSystem` and `Semantic.ModalCapybara.Semantics`
define the type system and the reduction semantics respectively.

Then, the `Semantic.ModalCapybara.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types are logical
predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates, and proves
properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.ModalCapybara.Fundamental` and `Semantic.ModalCapybara.Safety`
establishes semantic type soundness of Capture Calculus.
It proves the fundamental theorem: syntactic typing (which is defined in
`Semantic.ModalCapybara.TypeSystem`) implies semantic typing.
Then, it proves safety: well-typed programs are always progressive.
-/
