import Semantic.CaplessK.Denotation.Core
namespace CaplessK

mutual

/-- Extending handlers with a fresh label: the original denotation implies the extended one. -/
theorem shape_val_denot_extend_handlers_fresh
    {ctx : DenotCtx s} {S : Ty .shape s} {l : Nat} {D : Denot}
    (hfresh : l ∉ ctx.handlers.dom) :
    (Ty.shape_val_denot ctx S A).Imply (Ty.shape_val_denot (ctx.extend_handlers l D) S A) := by
  sorry

/-- Extending handlers with a fresh label: the original denotation implies the extended one. -/
theorem capt_val_denot_extend_handlers_fresh
    {ctx : DenotCtx s} {T : Ty .capt s} {l : Nat} {D : Denot}
    (hfresh : l ∉ ctx.handlers.dom) :
    (Ty.capt_val_denot ctx T).Imply (Ty.capt_val_denot (ctx.extend_handlers l D) T) := by
  sorry

/-- Extending handlers with a fresh label: the original denotation implies the extended one. -/
theorem exi_val_denot_extend_handlers_fresh
    {ctx : DenotCtx s} {E : Ty .exi s} {l : Nat} {D : Denot}
    (hfresh : l ∉ ctx.handlers.dom) :
    (Ty.exi_val_denot ctx E).Imply (Ty.exi_val_denot (ctx.extend_handlers l D) E) := by
  sorry

/-- Extending handlers with a fresh label: the original denotation implies the extended one. -/
theorem exi_exp_denot_extend_handlers_fresh
    {ctx : DenotCtx s} {E : Ty .exi s} {l : Nat} {D : Denot}
    (hfresh : l ∉ ctx.handlers.dom) :
    (Ty.exi_exp_denot ctx E A).Imply (Ty.exi_exp_denot (ctx.extend_handlers l D) E A) := by
  sorry

end

end CaplessK
