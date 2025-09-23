import Semantic.Fsub.Denotation
namespace Fsub

theorem sem_typ_var :
  Γ ⊨ (.var x) : (.singleton x) := by
  intro s e hts
  simp [Ty.exp_denot]
  constructor; constructor
  apply And.intro Reduce.red_refl _
  cases x
  case bound bx =>
    simp [Ty.val_denot]
    rfl
  case free fx =>
    simp [Ty.val_denot]
    rfl

theorem sem_typ_abs
  (ht : (Γ,x:T1) ⊨ e : T2) :
  Γ ⊨ (.abs T1 e) : (.arrow T1 T2) := by
  intro env store hts
  simp [Ty.exp_denot]
  constructor; constructor
  apply And.intro Reduce.red_refl _
  simp [Ty.val_denot]
  constructor; constructor
  constructor
  · rfl
  · unfold SemanticTyping at ht
    intro arg harg
    simp [Exp.from_TypeEnv_weaken_open]
    apply ht
    constructor
    { exact harg }
    { exact hts }

theorem sem_typ_tabs
  (ht : (Γ,X<:S) ⊨ e : T) :
  Γ ⊨ (.tabs S e) : (.poly S T) := by
  intro env store hts
  simp [Ty.exp_denot]
  constructor; constructor
  apply And.intro Reduce.red_refl _
  simp [Ty.val_denot]
  constructor; constructor
  constructor
  · rfl
  · unfold SemanticTyping at ht
    intro denot hdenot
    simp [Exp.from_TypeEnv_weaken_open_tvar (d:=denot)]
    apply ht
    constructor
    { exact hdenot }
    { exact hts }

theorem sem_typ_app
  (ht1 : Γ ⊨ (.var x) : (.arrow T1 T2))
  (ht2 : Γ ⊨ (.var y) : T1) :
  Γ ⊨ (.app x y) : (T2.subst (Subst.openVar x)) := by
  intro env store hts
  simp [Ty.exp_denot]
  unfold SemanticTyping at ht1 ht2
  simp [Ty.exp_denot, Ty.val_denot] at ht1
  sorry

theorem soundness
  (ht : Γ ⊢ e : T) :
  Γ ⊨ e : T := by
  induction ht
  case var => apply sem_typ_var
  case abs => grind [sem_typ_abs]
  case tabs => grind [sem_typ_tabs]
  case app => sorry
  all_goals sorry

end Fsub
