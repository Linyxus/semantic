import Semantic.CoreCapybara.Debruijn

import Semantic.CoreCapybara.Syntax

import Semantic.CoreCapybara.Substitution

import Semantic.CoreCapybara.TypeSystem

import Semantic.CoreCapybara.Semantics

import Semantic.CoreCapybara.Denotation

import Semantic.CoreCapybara.Fundamental

import Semantic.CoreCapybara.Safety

import Semantic.CoreCapybara.Semantics.Standardization

import Semantic.CoreCapybara.Semantics.Confluence

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

For the parallel (`par`) fragment, `Semantic.CoreCapybara.Semantics.Standardization` proves
standardization (every interleaving run to an answer matches a sequential one up to Mazurkiewicz
trace-equivalence), and `Semantic.CoreCapybara.Semantics.Confluence` (on the nominal/equivariance
layer `Semantic.CoreCapybara.Semantics.Equivariance`) proves confluence / Church–Rosser for
arbitrary partial reductions: any two interleavings of a well-formed program reconverge up to a
location permutation, `Trace.Equiv`, and reachability-equivalence of `par` capture annotations —
the semantic content of data-race freedom.  Both theorems are CARRIER-FREE: they need no `Safe`
hypothesis, because the separation content that commutes independent steps is carried by the
interleaving `Step`'s own `par` guards.

The legacy surface language (System Capybara) and its type-directed compiler
were frozen 2026-07-04 (fresh-start ruling) and DELETED from the tree
2026-07-06 as obsolete. Their last green state against the old core is branch
`capybara-translation-pre-rebase-2` (also `capybara-translation-pre-rebase`).
A new Capybara is being rebuilt from first principles — see
`roadmaps/translation.md`.
-/
