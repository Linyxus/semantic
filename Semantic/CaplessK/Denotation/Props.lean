import Semantic.CaplessK.Denotation.Core
namespace CaplessK

/-- Combining two Imply relations with Or. -/
lemma Denot.Imply.or {d1 d1' d2 d2' : Denot}
    (h1 : d1.Imply d1') (h2 : d2.Imply d2') :
    (d1.Or d2).Imply (d1'.Or d2') := by
  intro m e hor
  cases hor with
  | inl h => exact Or.inl (h1 m e h)
  | inr h => exact Or.inr (h2 m e h)

/-- Denot.Imply converts to Mpost.entails via as_mpost. -/
lemma Denot.Imply.as_mpost_entails {d1 d2 : Denot}
    (himp : d1.Imply d2) :
    d1.as_mpost.entails d2.as_mpost := by
  intro m e h
  exact himp m e h

/-- Extending handlers with a fresh label preserves denot_of_handlers (implication). -/
lemma denot_of_handlers_extend_imply
    {handlers : Finmap Nat Denot} {l : Nat} {D : Denot}
    (hfresh : l ∉ handlers.dom) :
    (denot_of_handlers handlers).Imply (denot_of_handlers (handlers.extend l D)) := by
  intro m e ⟨l', D', x, happly, heq, hD⟩
  refine ⟨l', D', x, ?_, heq, hD⟩
  simp only [Finmap.extend]
  -- Since handlers.apply l' = some D', we have l' ∈ handlers.dom
  have hl'_in_dom : l' ∈ handlers.dom := handlers.hasdom l' |>.mpr ⟨D', happly⟩
  -- Since l ∉ handlers.dom and l' ∈ handlers.dom, we have l' ≠ l
  have hne : l' ≠ l := fun h => hfresh (h ▸ hl'_in_dom)
  simp [hne, happly]

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
  cases T with
  | capt C S =>
    simp only [Ty.capt_val_denot]
    intro m e ⟨hsimp, hwf, hwf_cs, hshape⟩
    -- extend_handlers doesn't change env, so Subst.from_DenotCtx is unchanged
    have hsubst_eq : Subst.from_DenotCtx (ctx.extend_handlers l D) = Subst.from_DenotCtx ctx := rfl
    -- CaptureSet.denot only depends on env, so it's unchanged
    have hdenot_eq : C.denot (ctx.extend_handlers l D) m = C.denot ctx m := rfl
    rw [hsubst_eq, hdenot_eq]
    refine ⟨hsimp, hwf, hwf_cs, ?_⟩
    exact shape_val_denot_extend_handlers_fresh hfresh m e hshape

/-- Extending handlers with a fresh label: the original denotation implies the extended one. -/
theorem exi_val_denot_extend_handlers_fresh
    {ctx : DenotCtx s} {E : Ty .exi s} {l : Nat} {D : Denot}
    (hfresh : l ∉ ctx.handlers.dom) :
    (Ty.exi_val_denot ctx E).Imply (Ty.exi_val_denot (ctx.extend_handlers l D) E) := by
  cases E with
  | typ T =>
    -- exi_val_denot ctx (.typ T) = capt_val_denot ctx T
    simp only [Ty.exi_val_denot]
    exact capt_val_denot_extend_handlers_fresh hfresh
  | exi T =>
    simp only [Ty.exi_val_denot]
    intro m e h
    -- h : match resolve m.heap e with | some (.pack CS x) => ... | _ => False
    -- Goal: match resolve m.heap e with | some (.pack CS x) => ... | _ => False
    -- The match discriminant is the same, so we can split both
    generalize hres : resolve m.heap e = res at h ⊢
    cases res with
    | none => exact h
    | some v =>
      cases v with
      | pack CS x =>
        obtain ⟨hwf_cs, hcapt⟩ := h
        refine ⟨hwf_cs, ?_⟩
        -- Need: capt_val_denot ((ctx.extend_handlers l D).extend_cvar CS) T m (.var x)
        -- Have: capt_val_denot (ctx.extend_cvar CS) T m (.var x)
        -- Key: extend_handlers and extend_cvar commute
        have hcomm : (ctx.extend_handlers l D).extend_cvar CS =
                     (ctx.extend_cvar CS).extend_handlers l D := rfl
        rw [hcomm]
        -- l ∉ (ctx.extend_cvar CS).handlers.dom since extend_cvar doesn't change handlers
        have hfresh' : l ∉ (ctx.extend_cvar CS).handlers.dom := hfresh
        exact capt_val_denot_extend_handlers_fresh hfresh' m (.var x) hcapt
      | _ => exact h

/-- Extending handlers with a fresh label: the original denotation implies the extended one. -/
theorem exi_exp_denot_extend_handlers_fresh
    {ctx : DenotCtx s} {E : Ty .exi s} {l : Nat} {D : Denot}
    (hfresh : l ∉ ctx.handlers.dom) :
    (Ty.exi_exp_denot ctx E A).Imply (Ty.exi_exp_denot (ctx.extend_handlers l D) E A) := by
  intro m e heval
  simp only [Ty.exi_exp_denot] at heval ⊢
  -- The postcondition changes: Q1 = val_denot.Or handlers_denot
  -- to Q2 = extended_val_denot.Or extended_handlers_denot
  -- We show Q1.as_mpost.entails Q2.as_mpost
  apply eval_post_monotonic _ heval
  apply Denot.Imply.as_mpost_entails
  apply Denot.Imply.or
  · exact exi_val_denot_extend_handlers_fresh hfresh
  · exact denot_of_handlers_extend_imply hfresh

end

end CaplessK
