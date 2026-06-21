import Semantic.Capybara.Debruijn

import Semantic.Capybara.Syntax

import Semantic.Capybara.Substitution

import Semantic.Capybara.TypeSystem

/-!
# System Capybara: Syntax and Type System

This module defines the syntax and type system of System Capybara.
It is duplicated from `Semantic.CoreCapybara`, keeping only the static fragment.

`Semantic.Capybara.Syntax` defines the syntax of the system, in de Bruijn style.
Infrastructure for de Bruijn indices is defined in `Semantic.Capybara.Debruijn`.
Then, `Semantic.Capybara.Substitution` establishes substitution operations and
properties for the syntax.
On top of that, `Semantic.Capybara.TypeSystem` defines the type system.
-/
