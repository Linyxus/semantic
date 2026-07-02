import Semantic.CoreCapybara.Denotation.Core
import Semantic.CoreCapybara.Denotation.Rebind
import Semantic.CoreCapybara.Denotation.Retype

namespace CoreCapybara

open CoreCapybara.WP (WorldLe)

/-! # Killing capture variables

The `letin`/`unpack` typing rules type their continuations in a context where
the consumed peaks of the scrutinee's budget have been retagged to `.killed`
(`Ctx.kill_peaks`). This file provides the semantic counterpart
(`TypeEnv.kill_peaks`) and the transport lemmas relating the two:

- killing changes only the authority tag of a binding: all lookups except
  `lookup_authority`/`lookup_cvar_auth` are invariant, hence so are
  substitutions, peak computations, and type denotations;
- `EnvTyping` transports along simultaneous context/environment killing;
- the environment separation invariant `EnvSepWf` is antitone under killing
  (killing only removes demanded pairs). -/

/-! ## Context-side lemmas -/

theorem Ctx.kill_cvar_lookup_var {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (x : BVar s .var) :
    (Γ.kill_cvar c).lookup_var x = Γ.lookup_var x := by
  match Γ, c, x with
  | .push Γ (.cvar a cb), .here, .there x => rfl
  | .push Γ (.var T), .there c, .here => rfl
  | .push Γ b, .there c, .there x =>
    simp only [Ctx.kill_cvar, Ctx.lookup_var]
    rw [Ctx.kill_cvar_lookup_var Γ c x]

theorem Ctx.kill_cvar_lookup_tvar {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (X : BVar s .tvar) :
    (Γ.kill_cvar c).lookup_tvar X = Γ.lookup_tvar X := by
  match Γ, c, X with
  | .push Γ (.cvar a cb), .here, .there X => rfl
  | .push Γ (.tvar S), .there c, .here => rfl
  | .push Γ b, .there c, .there X =>
    simp only [Ctx.kill_cvar, Ctx.lookup_tvar]
    rw [Ctx.kill_cvar_lookup_tvar Γ c X]

theorem Ctx.kill_cvar_lookup_cvar {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (c' : BVar s .cvar) :
    (Γ.kill_cvar c).lookup_cvar c' = Γ.lookup_cvar c' := by
  match Γ, c, c' with
  | .push Γ (.cvar a cb), .here, .here => rfl
  | .push Γ (.cvar a cb), .here, .there c' => rfl
  | .push Γ (.cvar a cb), .there c, .here => rfl
  | .push Γ b, .there c, .there c' =>
    simp only [Ctx.kill_cvar, Ctx.lookup_cvar]
    rw [Ctx.kill_cvar_lookup_cvar Γ c c']

theorem Ctx.kill_cvar_lookup_lock {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (ℓ : BVar s .lock) :
    (Γ.kill_cvar c).lookup_lock ℓ = Γ.lookup_lock ℓ := by
  match Γ, c, ℓ with
  | .push Γ (.cvar a cb), .here, .there ℓ => rfl
  | .push Γ (.lock Ψ), .there c, .here => rfl
  | .push Γ b, .there c, .there ℓ =>
    simp only [Ctx.kill_cvar, Ctx.lookup_lock]
    rw [Ctx.kill_cvar_lookup_lock Γ c ℓ]

/-- Killing a capture variable sets its authority to `.killed`. -/
theorem Ctx.kill_cvar_lookup_authority_self {s : Sig} (Γ : Ctx s)
    (c : BVar s .cvar) :
    (Γ.kill_cvar c).lookup_authority c = .killed := by
  match Γ, c with
  | .push Γ (.cvar a cb), .here => rfl
  | .push Γ b, .there c =>
    simp only [Ctx.kill_cvar, Ctx.lookup_authority]
    exact Ctx.kill_cvar_lookup_authority_self Γ c

/-- Killing a capture variable leaves the authority of others unchanged. -/
theorem Ctx.kill_cvar_lookup_authority_ne {s : Sig} (Γ : Ctx s)
    {c c' : BVar s .cvar} (hne : c' ≠ c) :
    (Γ.kill_cvar c).lookup_authority c' = Γ.lookup_authority c' := by
  match Γ, c, c' with
  | .push Γ (.cvar a cb), .here, .here => exact absurd rfl hne
  | .push Γ (.cvar a cb), .here, .there c' => rfl
  | .push Γ (.cvar a cb), .there c, .here => rfl
  | .push Γ b, .there c, .there c' =>
    simp only [Ctx.kill_cvar, Ctx.lookup_authority]
    exact Ctx.kill_cvar_lookup_authority_ne Γ (fun h => hne (congrArg BVar.there h))

/-- Killing preserves context closedness (only authority tags change). -/
theorem Ctx.kill_cvar_isClosed {s : Sig} {Γ : Ctx s} {c : BVar s .cvar}
    (h : Γ.IsClosed) : (Γ.kill_cvar c).IsClosed := by
  match Γ, c with
  | .push Γ (.cvar a cb), .here =>
    cases h with
    | push hΓ hb =>
      cases hb with
      | cvar hcb => exact Ctx.IsClosed.push hΓ (Binding.IsClosed.cvar hcb)
  | .push Γ b, .there c =>
    cases h with
    | push hΓ hb =>
      simp only [Ctx.kill_cvar]
      exact Ctx.IsClosed.push (Ctx.kill_cvar_isClosed hΓ) hb

mutual

theorem CaptureSet.peaksVarBound_kill_cvar {s : Sig} (Γ : Ctx s)
    (c : BVar s .cvar) (a : Access) (x : BVar s .var) :
    CaptureSet.peaksVarBound (Γ.kill_cvar c) a x =
      CaptureSet.peaksVarBound Γ a x := by
  match Γ, c, x with
  | .push Γ (.var T), .there c, .here =>
    simp only [Ctx.kill_cvar]
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound]
    rw [CaptureSet.peaks_kill_cvar Γ c T.captureSet]
  | .push Γ (.cvar a0 cb), .here, .there x =>
    simp only [Ctx.kill_cvar]
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound]
  | .push Γ b, .there c, .there x =>
    simp only [Ctx.kill_cvar]
    rw [CaptureSet.peaksVarBound, CaptureSet.peaksVarBound]
    rw [CaptureSet.peaksVarBound_kill_cvar Γ c a x]
termination_by (sizeOf Γ, sizeOf x + 1)

/-- Peak resolution ignores authority tags: it is invariant under killing. -/
theorem CaptureSet.peaks_kill_cvar {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (C : CaptureSet s) :
    CaptureSet.peaks (Γ.kill_cvar c) C = CaptureSet.peaks Γ C := by
  match C with
  | .empty => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .union cs1 cs2 =>
    change CaptureSet.peaks (Γ.kill_cvar c) (cs1 ∪ cs2) = CaptureSet.peaks Γ (cs1 ∪ cs2)
    rw [CaptureSet.peaks_union, CaptureSet.peaks_union]
    rw [CaptureSet.peaks_kill_cvar Γ c cs1, CaptureSet.peaks_kill_cvar Γ c cs2]
  | .cvar a c' => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .var a (.free n) => rw [CaptureSet.peaks, CaptureSet.peaks]
  | .var a (.bound x) =>
    rw [CaptureSet.peaks, CaptureSet.peaks]
    exact CaptureSet.peaksVarBound_kill_cvar Γ c a x
termination_by (sizeOf Γ, sizeOf C)

end

theorem CaptureSet.peakset_kill_cvar {s : Sig} (Γ : Ctx s) (c : BVar s .cvar)
    (C : CaptureSet s) :
    C.peakset (Γ.kill_cvar c) = C.peakset Γ := by
  simp only [CaptureSet.peakset]
  congr 1
  exact CaptureSet.peaks_kill_cvar Γ c C

/-! Lifting the single-variable lemmas to `kill_peaks_cs`/`kill_peaks`. -/

theorem Ctx.kill_peaks_cs_lookup_var {s : Sig} (Γ : Ctx s) (K : CaptureSet s)
    (x : BVar s .var) :
    (Γ.kill_peaks_cs K).lookup_var x = Γ.lookup_var x := by
  induction K generalizing Γ with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change ((Γ.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_var x = Γ.lookup_var x
    rw [ih2, ih1]
  | cvar a c => exact Ctx.kill_cvar_lookup_var Γ c x
  | var a v => rfl

theorem Ctx.kill_peaks_cs_isClosed {s : Sig} {Γ : Ctx s} {K : CaptureSet s}
    (h : Γ.IsClosed) : (Γ.kill_peaks_cs K).IsClosed := by
  induction K generalizing Γ with
  | empty => exact h
  | union cs1 cs2 ih1 ih2 => exact ih2 (ih1 h)
  | cvar a c => exact Ctx.kill_cvar_isClosed h
  | var a v => exact h

theorem CaptureSet.peaks_kill_peaks_cs {s : Sig} (Γ : Ctx s) (K : CaptureSet s)
    (C : CaptureSet s) :
    CaptureSet.peaks (Γ.kill_peaks_cs K) C = CaptureSet.peaks Γ C := by
  induction K generalizing Γ with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change CaptureSet.peaks ((Γ.kill_peaks_cs cs1).kill_peaks_cs cs2) C =
      CaptureSet.peaks Γ C
    rw [ih2, ih1]
  | cvar a c => exact CaptureSet.peaks_kill_cvar Γ c C
  | var a v => rfl

theorem CaptureSet.peakset_kill_peaks_cs {s : Sig} (Γ : Ctx s) (K : CaptureSet s)
    (C : CaptureSet s) :
    C.peakset (Γ.kill_peaks_cs K) = C.peakset Γ := by
  simp only [CaptureSet.peakset]
  congr 1
  exact CaptureSet.peaks_kill_peaks_cs Γ K C

/-- The authority in a killed context is either the original or `.killed`. -/
theorem Ctx.kill_peaks_cs_lookup_authority {s : Sig} (Γ : Ctx s)
    (K : CaptureSet s) (c : BVar s .cvar) :
    (Γ.kill_peaks_cs K).lookup_authority c = Γ.lookup_authority c ∨
    (Γ.kill_peaks_cs K).lookup_authority c = .killed := by
  induction K generalizing Γ with
  | empty => exact Or.inl rfl
  | union cs1 cs2 ih1 ih2 =>
    change ((Γ.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_authority c =
        Γ.lookup_authority c ∨
      ((Γ.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_authority c = .killed
    rcases ih2 (Γ.kill_peaks_cs cs1) with h2 | h2
    · rw [h2]; exact ih1 Γ
    · exact Or.inr h2
  | cvar a c' =>
    by_cases h : c = c'
    · subst h
      exact Or.inr (Ctx.kill_cvar_lookup_authority_self Γ c)
    · exact Or.inl (Ctx.kill_cvar_lookup_authority_ne Γ h)
  | var a v => exact Or.inl rfl

/-! ## Environment-side: killing in a `TypeEnv` -/

/-- Sets the authority of the capture variable `c` to `.killed` in the
environment, leaving everything else unchanged. Mirrors `Ctx.kill_cvar`. -/
def TypeEnv.kill_cvar : TypeEnv s -> BVar s .cvar -> TypeEnv s
| .extend env (.cvar _ cs cap), .here => .extend env (.cvar .killed cs cap)
| .extend env info, .there c => .extend (env.kill_cvar c) info

/-- Kills every capture variable atom occurring in the capture set. Mirrors
`Ctx.kill_peaks_cs`. -/
def TypeEnv.kill_peaks_cs : TypeEnv s -> CaptureSet s -> TypeEnv s
| env, .empty => env
| env, .union cs1 cs2 => (env.kill_peaks_cs cs1).kill_peaks_cs cs2
| env, .cvar _ c => env.kill_cvar c
| env, .var _ _ => env

/-- Kills all peaks of the peak set. Mirrors `Ctx.kill_peaks`. -/
def TypeEnv.kill_peaks (env : TypeEnv s) (P : PeakSet s) : TypeEnv s :=
  env.kill_peaks_cs P.cs

theorem TypeEnv.kill_cvar_lookup_var {s : Sig} (env : TypeEnv s)
    (c : BVar s .cvar) (x : BVar s .var) :
    (env.kill_cvar c).lookup_var x = env.lookup_var x := by
  match env, c, x with
  | .extend env (.cvar a cs cap), .here, .there x => rfl
  | .extend env (.var n ps), .there c, .here => rfl
  | .extend env info, .there c, .there x =>
    simp only [TypeEnv.kill_cvar, TypeEnv.lookup_var]
    rw [TypeEnv.kill_cvar_lookup_var env c x]

theorem TypeEnv.kill_cvar_lookup_tvar {s : Sig} (env : TypeEnv s)
    (c : BVar s .cvar) (X : BVar s .tvar) :
    (env.kill_cvar c).lookup_tvar X = env.lookup_tvar X := by
  match env, c, X with
  | .extend env (.cvar a cs cap), .here, .there X => rfl
  | .extend env (.tvar d), .there c, .here => rfl
  | .extend env info, .there c, .there X =>
    simp only [TypeEnv.kill_cvar, TypeEnv.lookup_tvar]
    rw [TypeEnv.kill_cvar_lookup_tvar env c X]

theorem TypeEnv.kill_cvar_lookup_cvar {s : Sig} (env : TypeEnv s)
    (c : BVar s .cvar) (c' : BVar s .cvar) :
    (env.kill_cvar c).lookup_cvar c' = env.lookup_cvar c' := by
  match env, c, c' with
  | .extend env (.cvar a cs cap), .here, .here => rfl
  | .extend env (.cvar a cs cap), .here, .there c' => rfl
  | .extend env (.cvar a cs cap), .there c, .here => rfl
  | .extend env info, .there c, .there c' =>
    simp only [TypeEnv.kill_cvar, TypeEnv.lookup_cvar]
    rw [TypeEnv.kill_cvar_lookup_cvar env c c']

theorem TypeEnv.kill_cvar_lookup_cvar_auth_self {s : Sig} (env : TypeEnv s)
    (c : BVar s .cvar) :
    (env.kill_cvar c).lookup_cvar_auth c = .killed := by
  match env, c with
  | .extend env (.cvar a cs cap), .here => rfl
  | .extend env info, .there c =>
    simp only [TypeEnv.kill_cvar, TypeEnv.lookup_cvar_auth]
    exact TypeEnv.kill_cvar_lookup_cvar_auth_self env c

theorem TypeEnv.kill_cvar_lookup_cvar_auth_ne {s : Sig} (env : TypeEnv s)
    {c c' : BVar s .cvar} (hne : c' ≠ c) :
    (env.kill_cvar c).lookup_cvar_auth c' = env.lookup_cvar_auth c' := by
  match env, c, c' with
  | .extend env (.cvar a cs cap), .here, .here => exact absurd rfl hne
  | .extend env (.cvar a cs cap), .here, .there c' => rfl
  | .extend env (.cvar a cs cap), .there c, .here => rfl
  | .extend env info, .there c, .there c' =>
    simp only [TypeEnv.kill_cvar, TypeEnv.lookup_cvar_auth]
    exact TypeEnv.kill_cvar_lookup_cvar_auth_ne env (fun h => hne (congrArg BVar.there h))

/-- A variable that is `can_drop` after killing was `can_drop` before. -/
theorem TypeEnv.kill_cvar_can_drop_inv {s : Sig} {env : TypeEnv s}
    {c c' : BVar s .cvar}
    (h : (env.kill_cvar c).lookup_cvar_auth c' = .can_drop) :
    env.lookup_cvar_auth c' = .can_drop := by
  by_cases heq : c' = c
  · subst heq
    rw [TypeEnv.kill_cvar_lookup_cvar_auth_self] at h
    cases h
  · rwa [TypeEnv.kill_cvar_lookup_cvar_auth_ne env heq] at h

theorem Subst.from_TypeEnv_kill_cvar {s : Sig} {env : TypeEnv s}
    {c : BVar s .cvar} :
    Subst.from_TypeEnv (env.kill_cvar c) = Subst.from_TypeEnv env := by
  apply Subst.funext
  · intro x
    change Var.free ((env.kill_cvar c).lookup_var x).1 = Var.free (env.lookup_var x).1
    rw [TypeEnv.kill_cvar_lookup_var]
  · intro X
    rfl
  · intro C
    change ((env.kill_cvar c).lookup_cvar C).1 = (env.lookup_cvar C).1
    rw [TypeEnv.kill_cvar_lookup_cvar]

theorem compute_peaks_kill_cvar {s : Sig} (env : TypeEnv s) (c : BVar s .cvar)
    (C : CaptureSet s) :
    compute_peaks (env.kill_cvar c) C = compute_peaks env C := by
  induction C with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change (compute_peaks (env.kill_cvar c) cs1).union (compute_peaks (env.kill_cvar c) cs2) =
      (compute_peaks env cs1).union (compute_peaks env cs2)
    rw [ih1, ih2]
  | cvar a c' => rfl
  | var a v =>
    cases v with
    | free n => rfl
    | bound x =>
      change ((env.kill_cvar c).lookup_var x).2.cs.applyAccess a =
        (env.lookup_var x).2.cs.applyAccess a
      rw [TypeEnv.kill_cvar_lookup_var]

/-! ## Denotation invariance under killing

Type denotations read the environment only through `lookup_var`,
`lookup_tvar` and `lookup_cvar` (never through the authority), so they are
invariant under killing. We obtain this by transporting along a `Retype` at
the identity substitution. -/

def Retype.kill_cvar {env : TypeEnv s} (c : BVar s .cvar) :
    Retype env Subst.id (env.kill_cvar c) ⟨CaptureSet.empty, .empty⟩ where
  var := fun x => by
    change (env.lookup_var x).1 = ((env.kill_cvar c).lookup_var x).1
    rw [TypeEnv.kill_cvar_lookup_var]
  tvar := fun X => by
    intro k st m e
    simp only [Subst.id, PureTy.tvar, Ty.val_denot]
    rw [TypeEnv.kill_cvar_lookup_tvar]
  cvar := fun C => by
    change (env.lookup_cvar C).1 =
      ((env.kill_cvar c).lookup_cvar C).1.applyAccess (.M .epsilon)
    rw [TypeEnv.kill_cvar_lookup_cvar]
    rfl
theorem kill_cvar_val_denot {env : TypeEnv s} {c : BVar s .cvar}
    (T : Ty .capt s) :
    IDenot.Equiv (Ty.val_denot env T) (Ty.val_denot (env.kill_cvar c) T) := by
  have h := retype_val_denot (Retype.kill_cvar (env := env) c) T
  rwa [Ty.subst_id] at h

theorem kill_cvar_exi_val_denot {env : TypeEnv s} {c : BVar s .cvar}
    (T : Ty .exi s) :
    IDenot.Equiv (Ty.exi_val_denot env T) (Ty.exi_val_denot (env.kill_cvar c) T) := by
  have h := retype_exi_val_denot (Retype.kill_cvar (env := env) c) T
  rwa [Ty.subst_id] at h

theorem kill_cvar_exi_exp_denot {env : TypeEnv s} {c : BVar s .cvar}
    (T : Ty .exi s) (R : CapabilitySet) :
    IDenot.Equiv (Ty.exi_exp_denot env T R) (Ty.exi_exp_denot (env.kill_cvar c) T R) := by
  have h := retype_exi_exp_denot (Retype.kill_cvar (env := env) c) T (R := R)
  rwa [Ty.subst_id] at h

/-! ## `EnvTyping` transport along killing -/

theorem TypeEnv.Satisfy.kill_cvar {env : TypeEnv s} {c : BVar s .cvar}
    {Ψ : ModalCtx s} {m : Memory}
    (h : env.Satisfy Ψ m) : (env.kill_cvar c).Satisfy Ψ m where
  wf_sep := fun C hh => by
    rw [Subst.from_TypeEnv_kill_cvar]
    exact h.wf_sep C hh
  wf_mut := fun C mode hh => by
    rw [Subst.from_TypeEnv_kill_cvar]
    exact h.wf_mut C mode hh
  kind := fun C mode hh => by
    change CapabilitySet.HasKind
      ((C.subst (Subst.from_TypeEnv (env.kill_cvar c))).ground_denot m) mode
    rw [Subst.from_TypeEnv_kill_cvar]
    exact h.kind C mode hh
  sep := fun C1 C2 hh => by
    change CapabilitySet.Noninterference
      ((C1.subst (Subst.from_TypeEnv (env.kill_cvar c))).ground_denot m)
      ((C2.subst (Subst.from_TypeEnv (env.kill_cvar c))).ground_denot m)
    rw [Subst.from_TypeEnv_kill_cvar]
    exact h.sep C1 C2 hh

theorem EnvTyping.kill_cvar {s : Sig} {Γ : Ctx s} {env : TypeEnv s} {m : Memory}
    (c : BVar s .cvar) (h : EnvTyping Γ env k st m) :
    EnvTyping (Γ.kill_cvar c) (env.kill_cvar c) k st m := by
  match Γ, env, c with
  | .push Γ (.cvar a B), .extend env (.cvar a' cs cap), .here =>
    simp only [EnvTyping] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5, _, h7⟩ := h
    exact ⟨h1, h2, h3, h4, h5, rfl, h7⟩
  | .push Γ (.var T), .extend env (.var n ps), .there c =>
    simp only [EnvTyping] at h ⊢
    obtain ⟨hd, hps, h'⟩ := h
    refine ⟨?_, ?_, EnvTyping.kill_cvar c h'⟩
    · exact (kill_cvar_val_denot (c := c) T k st m (.var (.free n))).mp hd
    · rw [hps, CaptureSet.peakset_kill_cvar]
  | .push Γ (.tvar S), .extend env (.tvar d), .there c =>
    simp only [EnvTyping] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5, h'⟩ := h
    refine ⟨h1, h2, h3, ?_, h5, EnvTyping.kill_cvar c h'⟩
    intro j hjk st' m' hsub e hd
    exact (kill_cvar_val_denot (c := c) S.core j st' m' e).mp (h4 j hjk st' m' hsub e hd)
  | .push Γ (.cvar a B), .extend env (.cvar a' cs cap), .there c =>
    simp only [EnvTyping] at h ⊢
    obtain ⟨h1, h2, h3, h4, h5, h6, h'⟩ := h
    refine ⟨h1, ?_, ?_, h4, h5, h6, EnvTyping.kill_cvar c h'⟩
    · rwa [Subst.from_TypeEnv_kill_cvar]
    · show cap.BoundedBy (CaptureBound.denot (env.kill_cvar c) B m)
      cases B with
      | unbound => exact h3
      | bound bcs =>
        change cap.BoundedBy
          (.set ((bcs.subst (Subst.from_TypeEnv (env.kill_cvar c))).ground_denot m))
        rwa [Subst.from_TypeEnv_kill_cvar]
  | .push Γ (.lock Ψ), .extend env .lock, .there c =>
    simp only [EnvTyping] at h ⊢
    obtain ⟨h1, h'⟩ := h
    exact ⟨TypeEnv.Satisfy.kill_cvar h1, EnvTyping.kill_cvar c h'⟩

/-! ## Lifting to `kill_peaks_cs`/`kill_peaks` -/

theorem TypeEnv.kill_peaks_cs_lookup_var {s : Sig} (env : TypeEnv s)
    (K : CaptureSet s) (x : BVar s .var) :
    (env.kill_peaks_cs K).lookup_var x = env.lookup_var x := by
  induction K generalizing env with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change ((env.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_var x = env.lookup_var x
    rw [ih2, ih1]
  | cvar a c => exact TypeEnv.kill_cvar_lookup_var env c x
  | var a v => rfl

theorem TypeEnv.kill_peaks_cs_lookup_cvar {s : Sig} (env : TypeEnv s)
    (K : CaptureSet s) (c' : BVar s .cvar) :
    (env.kill_peaks_cs K).lookup_cvar c' = env.lookup_cvar c' := by
  induction K generalizing env with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change ((env.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_cvar c' = env.lookup_cvar c'
    rw [ih2, ih1]
  | cvar a c => exact TypeEnv.kill_cvar_lookup_cvar env c c'
  | var a v => rfl

theorem Subst.from_TypeEnv_kill_peaks_cs {s : Sig} {env : TypeEnv s}
    {K : CaptureSet s} :
    Subst.from_TypeEnv (env.kill_peaks_cs K) = Subst.from_TypeEnv env := by
  induction K generalizing env with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change Subst.from_TypeEnv ((env.kill_peaks_cs cs1).kill_peaks_cs cs2) =
      Subst.from_TypeEnv env
    rw [ih2, ih1]
  | cvar a c => exact Subst.from_TypeEnv_kill_cvar
  | var a v => rfl

theorem TypeEnv.kill_peaks_cs_can_drop_inv {s : Sig} {env : TypeEnv s}
    {K : CaptureSet s} {c : BVar s .cvar}
    (h : (env.kill_peaks_cs K).lookup_cvar_auth c = .can_drop) :
    env.lookup_cvar_auth c = .can_drop := by
  induction K generalizing env with
  | empty => exact h
  | union cs1 cs2 ih1 ih2 => exact ih1 (ih2 h)
  | cvar a c' => exact TypeEnv.kill_cvar_can_drop_inv h
  | var a v => exact h

/-- A killed variable stays killed under further killing. -/
theorem TypeEnv.kill_cvar_killed_mono {s : Sig} {env : TypeEnv s}
    {c c' : BVar s .cvar}
    (h : env.lookup_cvar_auth c' = .killed) :
    (env.kill_cvar c).lookup_cvar_auth c' = .killed := by
  by_cases heq : c' = c
  · subst heq; exact TypeEnv.kill_cvar_lookup_cvar_auth_self env c'
  · rwa [TypeEnv.kill_cvar_lookup_cvar_auth_ne env heq]

theorem TypeEnv.kill_peaks_cs_killed_mono {s : Sig} {env : TypeEnv s}
    {K : CaptureSet s} {c : BVar s .cvar}
    (h : env.lookup_cvar_auth c = .killed) :
    (env.kill_peaks_cs K).lookup_cvar_auth c = .killed := by
  induction K generalizing env with
  | empty => exact h
  | union cs1 cs2 ih1 ih2 => exact ih2 (ih1 h)
  | cvar a c' => exact TypeEnv.kill_cvar_killed_mono h
  | var a v => exact h

/-- Every capture variable atom of the killed set is `.killed` afterwards. -/
theorem TypeEnv.kill_peaks_cs_killed {s : Sig} {env : TypeEnv s}
    {K : CaptureSet s} {a : Access} {c : BVar s .cvar}
    (hsub : (CaptureSet.cvar a c) ⊆ K) :
    (env.kill_peaks_cs K).lookup_cvar_auth c = .killed := by
  induction K generalizing env with
  | empty => exact absurd hsub CaptureSet.cvar_not_subset_empty
  | union cs1 cs2 ih1 ih2 =>
    change ((env.kill_peaks_cs cs1).kill_peaks_cs cs2).lookup_cvar_auth c = .killed
    rcases CaptureSet.cvar_subset_union_inv hsub with h | h
    · exact TypeEnv.kill_peaks_cs_killed_mono (ih1 h)
    · exact ih2 h
  | cvar a' c' =>
    cases hsub
    exact TypeEnv.kill_cvar_lookup_cvar_auth_self env c
  | var a' v => exact absurd hsub CaptureSet.cvar_not_subset_var

theorem kill_peaks_cs_val_denot {env : TypeEnv s} {K : CaptureSet s}
    (T : Ty .capt s) :
    IDenot.Equiv (Ty.val_denot env T) (Ty.val_denot (env.kill_peaks_cs K) T) := by
  induction K generalizing env with
  | empty => exact IDenot.equiv_refl _
  | union cs1 cs2 ih1 ih2 =>
    exact IDenot.equiv_trans (ih1 (env := env))
      (ih2 (env := env.kill_peaks_cs cs1))
  | cvar a c => exact kill_cvar_val_denot T
  | var a v => exact IDenot.equiv_refl _

theorem kill_peaks_cs_exi_val_denot {env : TypeEnv s} {K : CaptureSet s}
    (T : Ty .exi s) :
    IDenot.Equiv (Ty.exi_val_denot env T) (Ty.exi_val_denot (env.kill_peaks_cs K) T) := by
  induction K generalizing env with
  | empty => exact IDenot.equiv_refl _
  | union cs1 cs2 ih1 ih2 =>
    exact IDenot.equiv_trans (ih1 (env := env))
      (ih2 (env := env.kill_peaks_cs cs1))
  | cvar a c => exact kill_cvar_exi_val_denot T
  | var a v => exact IDenot.equiv_refl _

theorem kill_peaks_cs_exi_exp_denot {env : TypeEnv s} {K : CaptureSet s}
    (T : Ty .exi s) (R : CapabilitySet) :
    IDenot.Equiv (Ty.exi_exp_denot env T R) (Ty.exi_exp_denot (env.kill_peaks_cs K) T R) := by
  induction K generalizing env with
  | empty => exact IDenot.equiv_refl _
  | union cs1 cs2 ih1 ih2 =>
    exact IDenot.equiv_trans (ih1 (env := env))
      (ih2 (env := env.kill_peaks_cs cs1))
  | cvar a c => exact kill_cvar_exi_exp_denot T R
  | var a v => exact IDenot.equiv_refl _

theorem EnvTyping.kill_peaks_cs {s : Sig} {Γ : Ctx s} {env : TypeEnv s}
    {k : Nat} {st : StoreTyping k} {m : Memory} (K : CaptureSet s) (h : EnvTyping Γ env k st m) :
    EnvTyping (Γ.kill_peaks_cs K) (env.kill_peaks_cs K) k st m := by
  induction K generalizing Γ env with
  | empty => exact h
  | union cs1 cs2 ih1 ih2 =>
    change EnvTyping ((Γ.kill_peaks_cs cs1).kill_peaks_cs cs2)
      ((env.kill_peaks_cs cs1).kill_peaks_cs cs2) k st m
    exact ih2 (ih1 h)
  | cvar a c => exact EnvTyping.kill_cvar c h
  | var a v => exact h

theorem EnvTyping.kill_peaks {s : Sig} {Γ : Ctx s} {env : TypeEnv s}
    {k : Nat} {st : StoreTyping k} {m : Memory} (P : PeakSet s) (h : EnvTyping Γ env k st m) :
    EnvTyping (Γ.kill_peaks P) (env.kill_peaks P) k st m :=
  EnvTyping.kill_peaks_cs P.cs h

/-! ## The `EnvSepWf` kit -/

theorem TypeEnv.EnvSepWf.extend_var {env : TypeEnv s} {n : Nat} {ps : PeakSet s}
    (h : env.EnvSepWf) : (env.extend_var n ps).EnvSepWf := by
  intro c1 c2 hne h1 h2
  cases c1 with
  | there c1 =>
    cases c2 with
    | there c2 =>
      exact h c1 c2 (fun heq => hne (congrArg BVar.there heq)) h1 h2

theorem TypeEnv.EnvSepWf.extend_tvar {env : TypeEnv s} {d : IDenot}
    (h : env.EnvSepWf) : (env.extend_tvar d).EnvSepWf := by
  intro c1 c2 hne h1 h2
  cases c1 with
  | there c1 =>
    cases c2 with
    | there c2 =>
      exact h c1 c2 (fun heq => hne (congrArg BVar.there heq)) h1 h2

theorem TypeEnv.EnvSepWf.extend_lock {env : TypeEnv s}
    (h : env.EnvSepWf) : (env.extend_lock).EnvSepWf := by
  intro c1 c2 hne h1 h2
  cases c1 with
  | there c1 =>
    cases c2 with
    | there c2 =>
      exact h c1 c2 (fun heq => hne (congrArg BVar.there heq)) h1 h2

/-- Extending with a non-droppable capture variable adds no demanded pairs. -/
theorem TypeEnv.EnvSepWf.extend_cvar_access_only {env : TypeEnv s}
    {cs : CaptureSet {}} {cap : CapabilitySet}
    (h : env.EnvSepWf) : (env.extend_cvar cs cap .access_only).EnvSepWf := by
  intro c1 c2 hne h1 h2
  cases c1 with
  | here => cases h1
  | there c1 =>
    cases c2 with
    | here => cases h2
    | there c2 =>
      exact h c1 c2 (fun heq => hne (congrArg BVar.there heq)) h1 h2

/-- Killing only removes demanded pairs: `EnvSepWf` is preserved. -/
theorem TypeEnv.EnvSepWf.kill_cvar {env : TypeEnv s} {c : BVar s .cvar}
    (h : env.EnvSepWf) : (env.kill_cvar c).EnvSepWf := by
  intro c1 c2 hne h1 h2
  rw [TypeEnv.kill_cvar_lookup_cvar, TypeEnv.kill_cvar_lookup_cvar]
  exact h c1 c2 hne (TypeEnv.kill_cvar_can_drop_inv h1)
    (TypeEnv.kill_cvar_can_drop_inv h2)

theorem TypeEnv.EnvSepWf.kill_peaks_cs {env : TypeEnv s} {K : CaptureSet s}
    (h : env.EnvSepWf) : (env.kill_peaks_cs K).EnvSepWf := by
  induction K generalizing env with
  | empty => exact h
  | union cs1 cs2 ih1 ih2 => exact ih2 (ih1 h)
  | cvar a c => exact TypeEnv.EnvSepWf.kill_cvar h
  | var a v => exact h

theorem TypeEnv.EnvSepWf.kill_peaks {env : TypeEnv s} {P : PeakSet s}
    (h : env.EnvSepWf) : (env.kill_peaks P).EnvSepWf :=
  TypeEnv.EnvSepWf.kill_peaks_cs h

/-! ## Commutation of killing with environment extension -/

theorem TypeEnv.kill_cvar_extend_cvar {env : TypeEnv s} {c : BVar s .cvar}
    {cs : CaptureSet {}} {cap : CapabilitySet} {a : Authority} :
    (env.kill_cvar c).extend_cvar cs cap a =
      (env.extend_cvar cs cap a).kill_cvar (.there c) := rfl

/-- Killing a weakened atom set in an extended environment kills the
original atoms below the extension. -/
theorem TypeEnv.kill_peaks_cs_extend_cvar {env : TypeEnv s} {K : CaptureSet s}
    {cs : CaptureSet {}} {cap : CapabilitySet} {a : Authority} :
    (env.kill_peaks_cs K).extend_cvar cs cap a =
      (env.extend_cvar cs cap a).kill_peaks_cs (K.rename Rename.succ) := by
  induction K generalizing env with
  | empty => rfl
  | union cs1 cs2 ih1 ih2 =>
    change ((env.kill_peaks_cs cs1).kill_peaks_cs cs2).extend_cvar cs cap a =
      ((env.extend_cvar cs cap a).kill_peaks_cs (cs1.rename Rename.succ)).kill_peaks_cs
        (cs2.rename Rename.succ)
    rw [ih2, ih1]
  | cvar a' c => rfl
  | var a' v => rfl

/-- Forward direction of `consumed`: a `.drop`-mode capture variable atom of a
capture set is an atom of its `consumed` part. -/
theorem CaptureSet.cvar_drop_subset_consumed {s : Sig} {C : CaptureSet s}
    {c : BVar s .cvar}
    (h : (CaptureSet.cvar .drop c) ⊆ C) :
    (CaptureSet.cvar .drop c) ⊆ C.consumed := by
  induction C with
  | empty => exact absurd h CaptureSet.cvar_not_subset_empty
  | union cs1 cs2 ih1 ih2 =>
    rcases CaptureSet.cvar_subset_union_inv h with h' | h'
    · exact CaptureSet.Subset.union_right_left (ih1 h')
    · exact CaptureSet.Subset.union_right_right (ih2 h')
  | cvar a' c' =>
    obtain ⟨ha, hc⟩ := CaptureSet.cvar_subset_cvar_inv h
    subst hc
    cases ha
    exact .refl
  | var a' v => exact absurd h CaptureSet.cvar_not_subset_var

end CoreCapybara
