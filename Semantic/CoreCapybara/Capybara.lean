import Semantic.CoreCapybara.Debruijn

import Semantic.CoreCapybara.Capybara.Syntax

import Semantic.CoreCapybara.Capybara.Substitution

import Semantic.CoreCapybara.Capybara.TypeSystem

/-!
# System Capybara: Syntax and Type System

This module defines the syntax and type system of System Capybara, the clean
surface language. It lives in the `CoreCapybara` namespace with all of its
constructs prefixed by `Capy` (e.g. `CapyTy`, `CapyExp`, `CapyHasType`) so that
it can coexist with the core calculus. It reuses the shared de Bruijn,
`CaptureSet` and `SepCtx` infrastructure from `Semantic.CoreCapybara`.

`Semantic.CoreCapybara.Capybara.Syntax` defines the syntax of the system, in
de Bruijn style, reusing `Semantic.CoreCapybara.Debruijn`.
Then, `Semantic.CoreCapybara.Capybara.Substitution` establishes substitution
operations and properties for the syntax.
On top of that, `Semantic.CoreCapybara.Capybara.TypeSystem` defines the type
system.
-/
