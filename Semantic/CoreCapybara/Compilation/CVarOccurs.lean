import Semantic.CoreCapybara.Compilation.OpenCVarSubtyp
open CoreCapybara
namespace Compilation

/-!
# Target-cvar occurrence and the codomain crux  (Option B)

The declarations that formerly lived here (`CapyCaptureSet.CvarMem`,
`CapyTy.SrcCvarFree`, `CapyCtx.SrcCvarFree`, `CapyTy.TgtCvarOccurs`,
`CapyTy.tgtCvarOccurs_implicit_cvar_absent`, …) were relocated *upstream* into
`OpenCVarSubtyp.lean` (before `CapyTy.compile_subst_subtyp`) so the substitution
lemma's droppability premise can be scoped by `TgtCvarOccurs T ctxOrig`.  This
file is retained as a stub; see `OpenCVarSubtyp.lean` for the definitions.
-/

end Compilation
