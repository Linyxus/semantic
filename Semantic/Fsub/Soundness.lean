import Semantic.Fsub.Denotation
import Semantic.Fsub.Eval
namespace Fsub

theorem sem_typ_var :
  Γ ⊨ (.var x) : (.singleton x) := by
  intro s e hts; simp only [Ty.exp_denot]
  apply Eval.eval_var
  cases x <;> simp [Ty.val_denot, Denot.as_post, Var.subst, interp_var]
  rfl

theorem sem_typ_abs
  (ht : (Γ,x:T1) ⊨ e : T2) :
  Γ ⊨ (.abs T1 e) : (.arrow T1 T2) := by
  intro env store hts; simp only [Ty.exp_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp only [Ty.val_denot, Denot.as_post]
    refine ⟨_, _, rfl, fun store' arg hsubsume harg => ?_⟩
    have key : (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openVar (.free arg))
             = e.subst (Subst.from_TypeEnv (env.extend_var arg)) :=
      Exp.from_TypeEnv_weaken_open
    exact key ▸ ht (env.extend_var arg) store' ⟨harg, env_typing_monotonic hts hsubsume⟩

theorem sem_typ_tabs
  (ht : (Γ,X<:S) ⊨ e : T) :
  Γ ⊨ (.tabs S e) : (.poly S T) := by
  intro env store hts; simp only [Ty.exp_denot]
  apply Eval.eval_val
  · simp [Exp.subst]; constructor
  · simp only [Ty.val_denot, Denot.as_post]
    refine ⟨_, _, rfl, fun H denot Hs hdenot_mono hdenot_trans himply => ?_⟩
    have key : (e.subst (Subst.from_TypeEnv env).lift).subst (Subst.openTVar .top)
             = e.subst (Subst.from_TypeEnv (env.extend_tvar denot)) :=
      Exp.from_TypeEnv_weaken_open_tvar
    exact key ▸ ht _ _ ⟨hdenot_mono, hdenot_trans, himply, env_typing_monotonic hts Hs⟩

theorem abs_val_denot_inv
  (hv : Ty.val_denot env (.arrow T1 T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ T0 e0 hv, store fx = some ⟨.abs T0 e0, hv⟩
    ∧ (∀ (store' : Heap) arg,
      store'.subsumes store ->
      (Ty.val_denot env T1 store' (.var (.free arg))) ->
      Ty.exp_denot (env.extend_var arg) T2 store' (e0.subst (Subst.openVar (.free arg)))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv; obtain ⟨T0, e0, hresolve, hfun⟩ := hv
    generalize hres : store fx = res at hresolve ⊢
    cases res
    case none => simp at hresolve
    case some v =>
      simp only at hresolve
      cases v; rename_i val hval; injection hresolve with hresolve; subst hresolve
      use fx, rfl, T0, e0, (by constructor)

theorem tabs_val_denot_inv
  (hv : Ty.val_denot env (.poly T1 T2) store (.var x)) :
  ∃ fx, x = .free fx
    ∧ ∃ T0 e0 hv, store fx = some ⟨.tabs T0 e0, hv⟩
    ∧ (∀ (s' : Heap) (denot : Denot),
      s'.subsumes store ->
      denot.is_monotonic ->
      denot.is_transparent ->
      denot.ImplyAfter s' (Ty.val_denot env T1) ->
      Ty.exp_denot (env.extend_tvar denot) T2 s' (e0.subst (Subst.openTVar .top))) := by
  cases x with
  | bound bx => cases bx
  | free fx =>
    simp only [Ty.val_denot, resolve] at hv; generalize hres : store fx = res
    cases res
    case none => aesop
    case some v =>
      simp only [hres] at hv; obtain ⟨T0, e0, htabs, hfun⟩ := hv
      use fx, rfl, T0, e0, by constructor
      cases v with
      | mk unwrap isVal =>
        simp only at htabs; injection htabs with htabs; subst htabs
        exact ⟨hres, hfun⟩

theorem interp_var_subst (x : Var s) :
  .free (interp_var env x) = x.subst (Subst.from_TypeEnv env) := by
  cases x <;> rfl

theorem var_exp_denot_inv
  (hv : Ty.exp_denot env T store (.var x)) :
  Ty.val_denot env T store (.var x) := by
  simp only [Ty.exp_denot] at hv; cases hv
  case eval_val hv _ => cases hv
  case eval_var hQ => exact hQ

theorem closed_var_inv (x : Var {}) :
  ∃ fx, x = .free fx := by
  cases x with
  | bound bx => cases bx
  | free fx => use fx

theorem sem_typ_app
  (ht1 : Γ ⊨ (.var x) : (.arrow T1 T2))
  (ht2 : Γ ⊨ (.var y) : T1) :
  Γ ⊨ (.app x y) : (T2.subst (Subst.openVar y)) := by
  intro env store hts; have h1 := ht1 env store hts; simp only [Exp.subst] at h1
  have h1' := var_exp_denot_inv h1
  have ⟨fx, hfx, T0, hbody, _, hlk, hfun⟩ := abs_val_denot_inv h1'
  simp only [Exp.subst, hfx]
  have h2 := ht2 env store hts; simp only [Exp.subst] at h2
  have h2' := var_exp_denot_inv h2
  have ⟨farg, hfarg⟩ := closed_var_inv (y.subst (Subst.from_TypeEnv env))
  have heq : farg = interp_var env y := by
    rw [← interp_var_subst (env:=env) (x:=y)] at hfarg; injection hfarg with heq; exact heq.symm
  subst farg
  have h2'' : Ty.val_denot env T1 store (.var (.free (interp_var env y))) := by
    simpa only [interp_var_subst] using h2'
  have := hfun store (interp_var env y) (Heap.subsumes_refl store) h2''
  simp only [Ty.exp_denot] at this ⊢; rw [← interp_var_subst (env:=env) (x:=y)]
  exact Eval.eval_apply hlk (eval_post_monotonic
    (Denot.imply_to_entails _ _ (Denot.equiv_to_imply
      (open_arg_val_denot (env:=env) (y:=y) (T:=T2))).1) this)

theorem sem_typ_tapp
  (ht : Γ ⊨ (.var x) : (.poly S T)) :
  Γ ⊨ (.tapp x S) : (T.subst (Subst.openTVar S)) := by
  intro env store hts; have h1 := ht env store hts; simp only [Exp.subst] at h1
  have ⟨fx, hfx, T0, e0, _, hlk, hfun⟩ := tabs_val_denot_inv (var_exp_denot_inv h1)
  simp only [Exp.subst, hfx]
  have hstep := hfun store (Ty.val_denot env S) (Heap.subsumes_refl store)
    (val_denot_is_monotonic (typed_env_is_monotonic hts))
    (val_denot_is_transparent (typed_env_is_transparent hts))
    (fun _ _ e he => he)
  simp only [Ty.exp_denot] at hstep ⊢; exact Eval.eval_tapply hlk (eval_post_monotonic
    (Denot.imply_to_entails _ _ (Denot.equiv_to_imply
      (open_targ_val_denot (env:=env) (S:=S) (T:=T))).1) hstep)

theorem sem_typ_letin
  (ht1 : Γ ⊨ e1 : T)
  (ht2 : (Γ,x:T) ⊨ e2 : (U.rename Rename.succ)) :
  Γ ⊨ (.letin e1 e2) : U := by
  intro env store hts; simp only [Exp.subst, Ty.exp_denot]
  apply Eval.eval_letin (Q1 := (Ty.val_denot env T).as_post)
  case hpred =>
    intro h1 h2 e hsub hQ; simp only [Denot.as_post] at hQ ⊢
    exact val_denot_is_monotonic (typed_env_is_monotonic hts) hsub hQ
  case a =>
    have h1 := ht1 env store hts; simp only [Ty.exp_denot] at h1; exact h1
  case h_val =>
    intro h1 v hs1 hv_isval hQ1 l' hfresh; simp only [Denot.as_post] at hQ1
    have hext : (h1.extend l' ⟨v, hv_isval⟩).subsumes h1 := Heap.extend_subsumes hfresh
    have ht2' := ht2 (env.extend_var l') (h1.extend l' ⟨v, hv_isval⟩)
    simp only [Ty.exp_denot] at ht2' ⊢; rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
    apply eval_post_monotonic _ (ht2' _)
    · apply Denot.imply_to_entails
      exact (Denot.equiv_to_imply (weaken_val_denot (env:=env) (x:=l') (T:=U))).2
    · constructor
      · exact val_denot_is_transparent (typed_env_is_transparent hts)
            (Heap.extend_lookup_eq h1 l' ⟨v, hv_isval⟩)
            (val_denot_is_monotonic (typed_env_is_monotonic hts) hext hQ1)
      · exact env_typing_monotonic hts (Heap.subsumes_trans hext hs1)
  case h_var =>
    intro h1 x hs1 hQ1; simp only [Denot.as_post] at hQ1
    obtain ⟨fx, hfx⟩ := closed_var_inv x; subst hfx
    have ht2' := ht2 (env.extend_var fx) h1
    simp only [Ty.exp_denot] at ht2' ⊢; rw [<-Exp.from_TypeEnv_weaken_open] at ht2'
    have hweaken := (Denot.equiv_to_imply (weaken_val_denot (env:=env) (x:=fx) (T:=U))).2
    exact eval_post_monotonic (Denot.imply_to_entails _ _ hweaken)
      (ht2' ⟨hQ1, env_typing_monotonic hts hs1⟩)

theorem typed_env_lookup_tvar
  (hts : EnvTyping Γ env store)
  (hx : Ctx.LookupTVar Γ X S) :
  (env.lookup_tvar X).ImplyAfter store (Ty.val_denot env S) := by
  induction hx generalizing store
  case here =>
    cases env; rename_i info0 env0; cases info0; rename_i d
    simp only [EnvTyping] at hts; simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]
    exact Denot.imply_after_trans hts.2.2.1 (fun h' _ e he => (tweaken_val_denot h' e).mp he)
  case there b _ ih =>
    cases env; rename_i info0 env0; cases info0
    case var =>
      rename_i n; cases b
      simp only [EnvTyping] at hts; simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]
      exact Denot.imply_after_trans (ih hts.2) (fun h' _ e he => (weaken_val_denot h' e).mp he)
    case tvar =>
      rename_i d; cases b
      simp only [EnvTyping] at hts; simp only [TypeEnv.lookup_tvar, TypeEnv.lookup]
      exact Denot.imply_after_trans (ih hts.2.2.2) (fun h' _ e he => (tweaken_val_denot h' e).mp he)

theorem typed_env_lookup_var
  (hts : EnvTyping Γ env store)
  (hx : Ctx.LookupVar Γ x T) :
  Ty.val_denot env T store (.var (.free (env.lookup_var x))) := by
  induction hx generalizing store
  case here =>
    rename_i Γ0 T0; cases env; rename_i info0 env0; cases info0; rename_i n
    simp only [EnvTyping] at hts; simp only [TypeEnv.lookup_var, TypeEnv.lookup]
    exact (Denot.equiv_to_imply (weaken_val_denot (env:=env0) (x:=n) (T:=T0))).1 store _ hts.1
  case there b =>
    rename_i k Γ0 x0 T0 binding hlk
    cases binding
    case var =>
      rename_i Tb
      cases env; rename_i info0 env0; cases info0; rename_i n
      simp only [EnvTyping] at hts; simp only [TypeEnv.lookup_var, TypeEnv.lookup]
      exact (Denot.equiv_to_imply (weaken_val_denot (env:=env0) (x:=n) (T:=T0))).1
        store _ (b hts.2)
    case tvar =>
      rename_i Sb
      cases env; rename_i info0 env0; cases info0; rename_i d
      simp only [EnvTyping] at hts; simp only [TypeEnv.lookup_var, TypeEnv.lookup]
      exact (Denot.equiv_to_imply (tweaken_val_denot (env:=env0) (d:=d) (T:=T0))).1
        store _ (b hts.2.2.2)

lemma sem_subtyp_poly
  (hS : SemSubtyp Γ S2 S1) -- contravariant in bound
  (hT : SemSubtyp (Γ,X<:S2) T1 T2) -- covariant in body, under extended context
  : SemSubtyp Γ (.poly S1 T1) (.poly S2 T2) := by
  intro type_env heap hts heap' hheap ans hans; simp only [Ty.val_denot] at hans ⊢
  obtain ⟨T0, e0, hresolve, hfun⟩ := hans
  refine ⟨T0, e0, hresolve, ?_⟩
  intro H denot Hsub hdenot_mono hdenot_trans himply_S2
  have himply_S1 : denot.ImplyAfter H (Ty.val_denot type_env S1) :=
    fun h' hs' e hdenot => hS type_env heap hts h'
      (Heap.subsumes_trans hs' (Heap.subsumes_trans Hsub hheap)) e (himply_S2 h' hs' e hdenot)
  have heval1 := hfun H denot Hsub hdenot_mono hdenot_trans himply_S1
  have henv' : EnvTyping (Γ,X<:S2) (type_env.extend_tvar denot) H :=
    ⟨hdenot_mono, hdenot_trans, himply_S2,
      env_typing_monotonic hts (Heap.subsumes_trans Hsub hheap)⟩
  exact Denot.apply_imply_at heval1
    (Denot.imply_after_to_imply_at (denot_implyat_lift (hT (type_env.extend_tvar denot) H henv')))

lemma sem_subtyp_arrow
  (hT : SemSubtyp Γ T2 T1)
  (hU : SemSubtyp (Γ,x:T2) U1 U2) :
  SemSubtyp Γ (.arrow T1 U1) (.arrow T2 U2) := by
  intro type_env heap hts heap' hheap ans hans; simp only [Ty.val_denot] at hans ⊢
  obtain ⟨T0, e0, hresolve, hfun⟩ := hans
  refine ⟨T0, e0, hresolve, fun H arg hheap1 ht_arg => ?_⟩
  have ht_arg' := hT type_env heap hts H (Heap.subsumes_trans hheap1 hheap) _ ht_arg
  have henv' : EnvTyping (Γ,x:T2) (type_env.extend_var arg) H :=
    ⟨ht_arg, env_typing_monotonic hts (Heap.subsumes_trans hheap1 hheap)⟩
  exact Denot.apply_imply_at (hfun H arg hheap1 ht_arg')
    (Denot.imply_after_to_imply_at (denot_implyat_lift (hU (type_env.extend_var arg) H henv')))

lemma sem_subtyp_top {T : Ty s} :
  SemSubtyp Γ T .top := by
  intro type_env heap hts heap' hheap e he
  grind [Ty.val_denot]

lemma sem_subtyp_refl {T : Ty s} :
  SemSubtyp Γ T T := by
  grind [SemSubtyp, Denot.ImplyAfter, Denot.ImplyAt]

lemma sem_subtyp_trans
  (hsub1 : SemSubtyp Γ T1 T2)
  (hsub2 : SemSubtyp Γ T2 T3) :
  SemSubtyp Γ T1 T3 := by
  intro type_env heap hts heap' hheap
  exact Denot.implyat_trans (hsub1 type_env heap hts heap' hheap)
    (hsub2 type_env heap hts heap' hheap)

lemma sem_subtyp_tvar
  (hX : Ctx.LookupTVar Γ X S) :
  SemSubtyp Γ (.tvar X) S := by
  intro type_env heap hts heap' hheap; simp only [Ty.val_denot]
  exact typed_env_lookup_tvar hts hX heap' hheap

lemma sem_subtyp_singleton
  (hx : Ctx.LookupVar Γ x T) :
  SemSubtyp Γ (.singleton (.bound x)) T := by
  intro type_env heap hts heap' hheap ans hans
  simp only [Ty.val_denot, interp_var] at hans; subst hans
  exact val_denot_is_monotonic (typed_env_is_monotonic hts) hheap (typed_env_lookup_var hts hx)

theorem fundamental_subtyp
  (hsub : Subtyp Γ T1 T2) :
  SemSubtyp Γ T1 T2 := by
  induction hsub with
  | top => exact sem_subtyp_top
  | refl => exact sem_subtyp_refl
  | trans _ _ => exact sem_subtyp_trans ‹_› ‹_›
  | tvar => exact sem_subtyp_tvar ‹_›
  | singleton => exact sem_subtyp_singleton ‹_›
  | arrow _ _ => exact sem_subtyp_arrow ‹_› ‹_›
  | poly _ _ => exact sem_subtyp_poly ‹_› ‹_›

theorem sem_typ_subtyp
  (ht : Γ ⊨ e : T1)
  (hsub : Subtyp Γ T1 T2) :
  Γ ⊨ e : T2 := by
  intro env store hts; have h1 := ht env store hts; simp only [Ty.exp_denot] at h1 ⊢
  exact eval_post_monotonic_general (Denot.imply_after_to_entails_after
    (fundamental_subtyp hsub env store hts)) h1

/-- The fundamental theorem of semantic type soundness. -/
theorem fundamental
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht with
  | var => exact sem_typ_var
  | abs _ => exact sem_typ_abs ‹_›
  | tabs _ => exact sem_typ_tabs ‹_›
  | app _ _ => exact sem_typ_app ‹_› ‹_›
  | tapp _ => exact sem_typ_tapp ‹_›
  | letin _ _ => exact sem_typ_letin ‹_› ‹_›
  | subtyp _ _ => exact sem_typ_subtyp ‹_› ‹_›

end Fsub
