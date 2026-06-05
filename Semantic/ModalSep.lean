import Semantic.ModalSep.Debruijn

import Semantic.ModalSep.Syntax

import Semantic.ModalSep.Substitution

import Semantic.ModalSep.TypeSystem

import Semantic.ModalSep.Semantics

import Semantic.ModalSep.Denotation

import Semantic.ModalSep.Fundamental

import Semantic.ModalSep.Safety

/-!
# Semantic Type Soundness for ModalSep

This module develops semantic type soundness of System ModalSep.
It is based on System Capybara.

`Semantic.ModalSep.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for debruijn indices is defined in `Semantic.ModalSep.Debruijn`.
Then, `Semantic.ModalSep.Substitution` establishes substitution operations and
properties for the syntax.
On top of that, `Semantic.ModalSep.TypeSystem` and `Semantic.ModalSep.Semantics`
define the type system and the reduction semantics respectively.

Then, the `Semantic.ModalSep.Denotation` module defines denotations for types.
Following a standard semantic type soundness approach, the denotations of types are logical
predicates on memory states and expressions.
This module defines the denotation function turning types into these predicates, and proves
properties on these denotations.
Semantic typing is then defined based on these type denotations.

Finally, `Semantic.ModalSep.Fundamental` and `Semantic.ModalSep.Safety`
establishes semantic type soundness of Capture Calculus.
It proves the fundamental theorem: syntactic typing (which is defined in
`Semantic.ModalSep.TypeSystem`) implies semantic typing.
Then, it proves safety: well-typed programs are always progressive.

This is considered an intermediate step towards the "actual" Capybara.
-/
