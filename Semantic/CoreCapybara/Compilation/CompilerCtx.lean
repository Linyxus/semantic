import Semantic.CoreCapybara
import Semantic.CoreCapybara.Capybara
open CoreCapybara
namespace Compilation

inductive SrcBinderInfo : Kind -> Sig -> Type where

inductive DstBinderInfo : Kind -> Type where

inductive SrcCtx : Sig -> Sig -> Type where
| empty : SrcCtx {} s
| cons :
  SrcBinderInfo k s1 ->
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

end Compilation
