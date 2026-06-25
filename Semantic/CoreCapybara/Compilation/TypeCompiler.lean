import Semantic.CoreCapybara.Compilation.CompilerCtx
open CoreCapybara
namespace Compilation

/-- Compiles a source capture set into the target -/
def CaptureSet.compile : CaptureSet s1 -> SrcCtx s1 s2 -> CaptureSet s2
| .empty, _ => .empty
| .union cs1 cs2, ctx => .union (CaptureSet.compile cs1 ctx) (CaptureSet.compile cs2 ctx)
| .cvar a c, ctx => .cvar a (ctx.lookupCVar c)
| .var a (.bound x), ctx => (ctx.lookupVar x).applyAccess a
| .var a (.free n), _ => .var a (.free n)

/-- Source and target type-sorts coincide; this maps between the two enums. -/
def CapyTySort.compile : CapyTySort -> TySort
| .capt => .capt
| .exi => .exi

/-- Compiles a source type into the target signature. -/
def CapyTy.compile : CapyTy sort s1 -> SrcCtx s1 s2 -> Ty (CapyTySort.compile sort) s2
-- trivial / structural cases
| .top, _ => .top
| .unit, _ => .unit
| .bool, _ => .bool
| .cap cs, ctx => .cap (CaptureSet.compile cs ctx)
| .cell cs .epsilon, ctx => .cell (CaptureSet.compile cs ctx)
| .cell cs .ro, ctx => .reader (CaptureSet.compile cs ctx)
| .typ T, ctx => .typ (CapyTy.compile T ctx)
| .tvar X, ctx => .tvar (ctx.lookupTVar X)
| .arrow _ _ _, _ => sorry
| .poly _ _ _, _ => sorry
| .cpoly _ _ _, _ => sorry
| .exi _, _ => sorry

end Compilation
