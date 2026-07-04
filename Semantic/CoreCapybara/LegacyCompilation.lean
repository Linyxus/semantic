import Semantic.CoreCapybara.LegacyCompilation.CompilerCtx
import Semantic.CoreCapybara.LegacyCompilation.TypeCompiler
import Semantic.CoreCapybara.LegacyCompilation.CompileLemmas
import Semantic.CoreCapybara.LegacyCompilation.ClosedLemmas
import Semantic.CoreCapybara.LegacyCompilation.ContextMorphism
import Semantic.CoreCapybara.LegacyCompilation.Coherence
import Semantic.CoreCapybara.LegacyCompilation.CoherenceMorphism
import Semantic.CoreCapybara.LegacyCompilation.SubstLemmas
import Semantic.CoreCapybara.LegacyCompilation.OpenCVarSubtyp
import Semantic.CoreCapybara.LegacyCompilation.Preservation

/-!
# Typed Compilation: Capybara → CoreCapybara

**FROZEN (2026-07-04, fresh-start ruling).** This is the LEGACY module,
quarantined as read-only reference and NOT imported by the build. Its last
green state against the old core is branch `capybara-translation-pre-rebase-2`;
after the core-capybara merge the in-tree copy is not expected to elaborate.
Superseded by the from-scratch Capybara — see `roadmaps/translation.md` (rev. 2).

This module develops the type-directed compiler from the surface language
System Capybara (`Semantic.CoreCapybara.LegacyCapybara`) into the core calculus
CoreCapybara.

`Semantic.CoreCapybara.LegacyCompilation.CompilerCtx` defines the compiler context,
which pairs the source typing context with a source→target map (`SrcCtx`) and a
target Core context (`DstCtx` / `Ctx`) over two signatures.
On top of that, `Semantic.CoreCapybara.LegacyCompilation.TypeCompiler` defines the
type compiler `CapyTy.compile`, translating surface types into core types.
-/
