import Semantic.CoreCapybara.Compilation.CompilerCtx
import Semantic.CoreCapybara.Compilation.TypeCompiler
import Semantic.CoreCapybara.Compilation.CompileLemmas
import Semantic.CoreCapybara.Compilation.Coherence
import Semantic.CoreCapybara.Compilation.Preservation

/-!
# Typed Compilation: Capybara → CoreCapybara

This module develops the type-directed compiler from the surface language
System Capybara (`Semantic.CoreCapybara.Capybara`) into the core calculus
CoreCapybara.

`Semantic.CoreCapybara.Compilation.CompilerCtx` defines the compiler context,
which pairs the source typing context with a source→target map (`SrcCtx`) and a
target Core context (`DstCtx` / `Ctx`) over two signatures.
On top of that, `Semantic.CoreCapybara.Compilation.TypeCompiler` defines the
type compiler `CapyTy.compile`, translating surface types into core types.
-/
