import Semantic.CoreCapybara.Debruijn

import Semantic.CoreCapybara.LegacyCapybara.Syntax

import Semantic.CoreCapybara.LegacyCapybara.Substitution

import Semantic.CoreCapybara.LegacyCapybara.TypeSystem

/-!
# System Capybara: Syntax and Type System

**FROZEN (2026-07-04, fresh-start ruling).** This is the LEGACY module,
quarantined as read-only reference and NOT imported by the build. Its last
green state against the old core is branch `capybara-translation-pre-rebase-2`;
after the core-capybara merge the in-tree copy is not expected to elaborate.
Superseded by the from-scratch Capybara — see `roadmaps/translation.md` (rev. 2).

This module defines the syntax and type system of System Capybara, the clean
surface language. It lives in the `CoreCapybara` namespace with all of its
constructs prefixed by `Capy` (e.g. `CapyTy`, `CapyExp`, `CapyHasType`) so that
it can coexist with the core calculus. It reuses the shared de Bruijn,
`CaptureSet` and `SepCtx` infrastructure from `Semantic.CoreCapybara`.

`Semantic.CoreCapybara.LegacyCapybara.Syntax` defines the syntax of the system, in
de Bruijn style, reusing `Semantic.CoreCapybara.Debruijn`.
Then, `Semantic.CoreCapybara.LegacyCapybara.Substitution` establishes substitution
operations and properties for the syntax.
On top of that, `Semantic.CoreCapybara.LegacyCapybara.TypeSystem` defines the type
system.
-/
