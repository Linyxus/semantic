import Semantic.CoreCapybara
import Semantic.CoreCapybara.Capybara
open CoreCapybara
namespace Compilation

inductive SrcBinderInfo : Kind -> Sig -> Type where
| var :
  BVar s .var ->
  CaptureSet s ->
  SrcBinderInfo .var s
| cvar : BVar s .cvar -> SrcBinderInfo .cvar s
| tvar : BVar s .tvar -> SrcBinderInfo .tvar s

inductive DstBinderInfo : Kind -> Type where

inductive SrcCtx : Sig -> Sig -> Type where
| empty : SrcCtx {} s
| cons :
  -- the binder info records the TARGET-sig (`s2`) image of this source binder
  SrcBinderInfo k s2 ->
  SrcCtx s1 s2 ->
  SrcCtx (s1,,k) s2

inductive DstCtx : Sig -> Type where
| empty : DstCtx {}
| cons :
  DstBinderInfo k ->
  DstCtx s ->
  DstCtx (s,,k)

structure CompilerCtx (s1 s2 : Sig) where
  capyCtx : CapyCtx s1
  srcCtx : SrcCtx s1 s2
  dstCtx : DstCtx s2

/-- Looks up the target capture variable that a source capture binder maps to. -/
def SrcCtx.lookupCVar : SrcCtx s1 s2 -> BVar s1 .cvar -> BVar s2 .cvar
| .cons (.cvar c) _, .here => c
| .cons _ rest, .there c => rest.lookupCVar c

/-- Looks up the target capture set that a source term variable stands for. -/
def SrcCtx.lookupVar : SrcCtx s1 s2 -> BVar s1 .var -> CaptureSet s2
| .cons (.var _ cs) _, .here => cs
| .cons _ rest, .there x => rest.lookupVar x

/-- Looks up the target type variable that a source type binder maps to. -/
def SrcCtx.lookupTVar : SrcCtx s1 s2 -> BVar s1 .tvar -> BVar s2 .tvar
| .cons (.tvar X) _, .here => X
| .cons _ rest, .there X => rest.lookupTVar X

/-- Renames the target-sig references stored in a binder info. -/
def SrcBinderInfo.rename : SrcBinderInfo k s2 -> Rename s2 s2' -> SrcBinderInfo k s2'
| .var x cs, ρ => .var (ρ.var x) (cs.rename ρ)
| .cvar c, ρ => .cvar (ρ.var c)
| .tvar X, ρ => .tvar (ρ.var X)

/-- Renames the (fixed) target signature of a whole source context. -/
def SrcCtx.rename : SrcCtx s1 s2 -> Rename s2 s2' -> SrcCtx s1 s2'
| .empty, _ => .empty
| .cons info rest, ρ => .cons (info.rename ρ) (rest.rename ρ)

/-- Weakens the target signature of a source context by one binder, so the
    existing source→target images stay valid after a fresh target binder is
    introduced. -/
def SrcCtx.weaken (ctx : SrcCtx s1 s2) : SrcCtx s1 (s2,,k) := ctx.rename Rename.succ

end Compilation
