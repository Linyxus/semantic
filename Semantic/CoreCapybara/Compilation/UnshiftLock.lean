import Semantic.CoreCapybara.Syntax.Exp

/-!
# Unshifting past a lock binder (TARGET syntax)

The target `HasType.wrap` rule (see `TypeSystem/Core.lean`) demands its body in the
syntactic image of `Rename.succ`.  The compile induction produces the body typed
under a pushed lock (signature `s,,Kind.lock`), so we must recover the un-shifted
witness.

This is *total* for a lock extension because no syntactic class ever stores a
`BVar _ .lock`: every variable occurring in syntax has kind `.var`/`.cvar`/`.tvar`,
and over signature `(s,,Kind.lock)` any `BVar (s,,Kind.lock) k` with `k ≠ .lock` is
necessarily `.there`-formed (the `.here` constructor would force `k = .lock`).

We build the family bottom-up, generalized over an inductive description
`LockIns s1 s2` of a lock inserted into `s1` at some depth to obtain `s2`.  Each
class-level lemma has the form
`∀ (t : Cls s2), ∃ t', t = t'.rename (ins.rename)`,
and the headline `Exp.unshift_lock` specializes `ins := .here`.
-/

namespace CoreCapybara

/-- `LockIns s1 s2` witnesses that `s2` is `s1` with a single `.lock` variable
    inserted at some depth. -/
inductive LockIns : Sig -> Sig -> Type where
| here : LockIns s (s,,Kind.lock)
| there : LockIns s1 s2 -> LockIns (s1,,k) (s2,,k)

/-- The renaming induced by a lock insertion: `Rename.succ` at the insertion point,
    lifted under each binder above it. -/
def LockIns.rename : LockIns s1 s2 -> Rename s1 s2
| .here => Rename.succ
| .there ins => ins.rename.lift

/-- Core inversion: any bound variable of non-lock kind over the target signature
    is the image of a bound variable over the source signature. -/
theorem LockIns.bvar_unshift {s1 s2 : Sig} (ins : LockIns s1 s2) :
    ∀ {k : Kind} (x : BVar s2 k), k ≠ Kind.lock →
      ∃ x' : BVar s1 k, x = ins.rename.var x' := by
  induction ins with
  | here =>
    intro k x hk
    cases x with
    | here => exact absurd rfl hk
    | there x' => exact ⟨x', rfl⟩
  | there ins ih =>
    intro k x hk
    cases x with
    | here => exact ⟨.here, rfl⟩
    | there x' =>
      obtain ⟨x'', rfl⟩ := ih x' hk
      exact ⟨.there x'', rfl⟩

/-- A term variable unshifts past a lock insertion. -/
theorem Var.unshiftLockIns {s2 : Sig} (x : Var .var s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ x' : Var .var s1, x = x'.rename ins.rename := by
  intro s1 ins
  cases x with
  | bound b =>
    obtain ⟨b', rfl⟩ := LockIns.bvar_unshift ins b (by decide)
    exact ⟨.bound b', rfl⟩
  | free n => exact ⟨.free n, rfl⟩

/-- A capture set unshifts past a lock insertion. -/
theorem CaptureSet.unshiftLockIns {s2 : Sig} (cs : CaptureSet s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ cs' : CaptureSet s1, cs = cs'.rename ins.rename := by
  induction cs with
  | empty => intro s1 ins; exact ⟨.empty, rfl⟩
  | union cs1 cs2 ih1 ih2 =>
    intro s1 ins
    obtain ⟨cs1', rfl⟩ := ih1 ins
    obtain ⟨cs2', rfl⟩ := ih2 ins
    exact ⟨.union cs1' cs2', rfl⟩
  | var a x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    exact ⟨.var a x', rfl⟩
  | cvar a x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := LockIns.bvar_unshift ins x (by decide)
    exact ⟨.cvar a x', rfl⟩

/-- A capture bound unshifts past a lock insertion. -/
theorem CaptureBound.unshiftLockIns {s2 : Sig} (cb : CaptureBound s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ cb' : CaptureBound s1, cb = cb'.rename ins.rename := by
  intro s1 ins
  cases cb with
  | unbound => exact ⟨.unbound, rfl⟩
  | bound cs =>
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    exact ⟨.bound cs', rfl⟩

/-- A separation context unshifts past a lock insertion. -/
theorem SepCtx.unshiftLockIns {s2 : Sig} (K : SepCtx s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ K' : SepCtx s1, K = K'.rename ins.rename := by
  induction K with
  | empty => intro s1 ins; exact ⟨.empty, rfl⟩
  | cons K C ih =>
    intro s1 ins
    obtain ⟨K', rfl⟩ := ih ins
    obtain ⟨C', rfl⟩ := CaptureSet.unshiftLockIns C ins
    exact ⟨.cons K' C', rfl⟩

/-- A mutability context unshifts past a lock insertion. -/
theorem MutabilityCtx.unshiftLockIns {s2 : Sig} (K : MutabilityCtx s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ K' : MutabilityCtx s1, K = K'.rename ins.rename := by
  induction K with
  | empty => intro s1 ins; exact ⟨.empty, rfl⟩
  | cons K C m ih =>
    intro s1 ins
    obtain ⟨K', rfl⟩ := ih ins
    obtain ⟨C', rfl⟩ := CaptureSet.unshiftLockIns C ins
    exact ⟨.cons K' C' m, rfl⟩

/-- A modal context unshifts past a lock insertion. -/
theorem ModalCtx.unshiftLockIns {s2 : Sig} (Ψ : ModalCtx s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ Ψ' : ModalCtx s1, Ψ = Ψ'.rename ins.rename := by
  intro s1 ins
  obtain ⟨sep, mu⟩ := Ψ
  obtain ⟨sep', rfl⟩ := SepCtx.unshiftLockIns sep ins
  obtain ⟨mu', rfl⟩ := MutabilityCtx.unshiftLockIns mu ins
  exact ⟨⟨sep', mu'⟩, rfl⟩

/-- Emptiness of a capture set is reflected by renaming: if the renamed set is
    empty, so is the original. -/
theorem CaptureSet.IsEmpty.rename_inv {s1 s2 : Sig} {cs : CaptureSet s1} {ρ : Rename s1 s2}
    (h : (cs.rename ρ).IsEmpty) : cs.IsEmpty := by
  induction cs with
  | empty => exact .empty
  | union cs1 cs2 ih1 ih2 =>
    simp only [CaptureSet.rename] at h
    cases h with
    | union h1 h2 => exact .union (ih1 h1) (ih2 h2)
  | var a x =>
    simp only [CaptureSet.rename] at h
    cases h
  | cvar a x =>
    simp only [CaptureSet.rename] at h
    cases h

/-- A type unshifts past a lock insertion. -/
theorem Ty.unshiftLockIns {sort : TySort} {s2 : Sig} (T : Ty sort s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ T' : Ty sort s1, T = T'.rename ins.rename := by
  induction T with
  | top => intro s1 ins; exact ⟨.top, rfl⟩
  | tvar x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := LockIns.bvar_unshift ins x (by decide)
    exact ⟨.tvar x', rfl⟩
  | arrow T1 cs T2 ih1 ih2 =>
    intro s1 ins
    obtain ⟨T1', rfl⟩ := ih1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨T2', rfl⟩ := ih2 ins.there
    exact ⟨.arrow T1' cs' T2', rfl⟩
  | poly T1 cs T2 ih1 ih2 =>
    intro s1 ins
    obtain ⟨T1', rfl⟩ := ih1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨T2', rfl⟩ := ih2 ins.there
    exact ⟨.poly T1' cs' T2', rfl⟩
  | cpoly cb cs T ih =>
    intro s1 ins
    obtain ⟨cb', rfl⟩ := CaptureBound.unshiftLockIns cb ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨T', rfl⟩ := ih ins.there
    exact ⟨.cpoly cb' cs' T', rfl⟩
  | modal cs Ψ T ih =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨Ψ', rfl⟩ := ModalCtx.unshiftLockIns Ψ ins
    obtain ⟨T', rfl⟩ := ih ins
    exact ⟨.modal cs' Ψ' T', rfl⟩
  | cap cs =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    exact ⟨.cap cs', rfl⟩
  | cell cs =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    exact ⟨.cell cs', rfl⟩
  | reader cs =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    exact ⟨.reader cs', rfl⟩
  | unit => intro s1 ins; exact ⟨.unit, rfl⟩
  | bool => intro s1 ins; exact ⟨.bool, rfl⟩
  | exi T ih =>
    intro s1 ins
    obtain ⟨T', rfl⟩ := ih ins.there
    exact ⟨.exi T', rfl⟩
  | typ T ih =>
    intro s1 ins
    obtain ⟨T', rfl⟩ := ih ins
    exact ⟨.typ T', rfl⟩

/-- A pure type unshifts past a lock insertion. -/
theorem PureTy.unshiftLockIns {s2 : Sig} (T : PureTy s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ T' : PureTy s1, T = T'.rename ins.rename := by
  intro s1 ins
  obtain ⟨core, p⟩ := T
  obtain ⟨core', hcore⟩ := Ty.unshiftLockIns core ins
  have hp' : core'.IsPureType := by
    have hpc : core.captureSet.IsEmpty := p
    rw [hcore, Ty.captureSet_rename] at hpc
    exact CaptureSet.IsEmpty.rename_inv hpc
  refine ⟨⟨core', hp'⟩, ?_⟩
  subst hcore
  rfl

/-- An expression unshifts past a lock insertion. -/
theorem Exp.unshiftLockIns {s2 : Sig} (e : Exp s2) :
    ∀ {s1 : Sig} (ins : LockIns s1 s2), ∃ e' : Exp s1, e = e'.rename ins.rename := by
  induction e with
  | var x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    exact ⟨.var x', rfl⟩
  | abs cs T e ih =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨T', rfl⟩ := Ty.unshiftLockIns T ins
    obtain ⟨e', rfl⟩ := ih ins.there
    exact ⟨.abs cs' T' e', rfl⟩
  | tabs cs T e ih =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨T', rfl⟩ := PureTy.unshiftLockIns T ins
    obtain ⟨e', rfl⟩ := ih ins.there
    exact ⟨.tabs cs' T' e', rfl⟩
  | cabs cs cb e ih =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨cb', rfl⟩ := CaptureBound.unshiftLockIns cb ins
    obtain ⟨e', rfl⟩ := ih ins.there
    exact ⟨.cabs cs' cb' e', rfl⟩
  | boxed cs Ψ e ih =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨Ψ', rfl⟩ := ModalCtx.unshiftLockIns Ψ ins
    obtain ⟨e', rfl⟩ := ih ins
    exact ⟨.boxed cs' Ψ' e', rfl⟩
  | reader x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    exact ⟨.reader x', rfl⟩
  | alloc x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    exact ⟨.alloc x', rfl⟩
  | drop x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    exact ⟨.drop x', rfl⟩
  | pack cs x =>
    intro s1 ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    exact ⟨.pack cs' x', rfl⟩
  | app x y =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    obtain ⟨y', rfl⟩ := Var.unshiftLockIns y ins
    exact ⟨.app x' y', rfl⟩
  | tapp x T =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    obtain ⟨T', rfl⟩ := PureTy.unshiftLockIns T ins
    exact ⟨.tapp x' T', rfl⟩
  | capp x cs =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    obtain ⟨cs', rfl⟩ := CaptureSet.unshiftLockIns cs ins
    exact ⟨.capp x' cs', rfl⟩
  | unwrap x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    exact ⟨.unwrap x', rfl⟩
  | letin e1 e2 ih1 ih2 =>
    intro s1 ins
    obtain ⟨e1', rfl⟩ := ih1 ins
    obtain ⟨e2', rfl⟩ := ih2 ins.there
    exact ⟨.letin e1' e2', rfl⟩
  | unpack e1 e2 ih1 ih2 =>
    intro s1 ins
    obtain ⟨e1', rfl⟩ := ih1 ins
    obtain ⟨e2', rfl⟩ := ih2 ins.there.there
    exact ⟨.unpack e1' e2', rfl⟩
  | unit => intro s1 ins; exact ⟨.unit, rfl⟩
  | btrue => intro s1 ins; exact ⟨.btrue, rfl⟩
  | bfalse => intro s1 ins; exact ⟨.bfalse, rfl⟩
  | read x =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    exact ⟨.read x', rfl⟩
  | write x y =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    obtain ⟨y', rfl⟩ := Var.unshiftLockIns y ins
    exact ⟨.write x' y', rfl⟩
  | cond x e2 e3 ih2 ih3 =>
    intro s1 ins
    obtain ⟨x', rfl⟩ := Var.unshiftLockIns x ins
    obtain ⟨e2', rfl⟩ := ih2 ins
    obtain ⟨e3', rfl⟩ := ih3 ins
    exact ⟨.cond x' e2' e3', rfl⟩
  | par C1 C2 e1 e2 ih1 ih2 =>
    intro s1 ins
    obtain ⟨C1', rfl⟩ := CaptureSet.unshiftLockIns C1 ins
    obtain ⟨C2', rfl⟩ := CaptureSet.unshiftLockIns C2 ins
    obtain ⟨e1', rfl⟩ := ih1 ins
    obtain ⟨e2', rfl⟩ := ih2 ins
    exact ⟨.par C1' C2' e1' e2', rfl⟩

/-- **Headline lemma.** An expression typed under a pushed lock binder is in the
    syntactic image of `Rename.succ`; the un-shifted witness lives over the
    original signature. -/
theorem Exp.unshift_lock {s : Sig} (e : Exp (s,,Kind.lock)) :
    ∃ e' : Exp s, e = e'.rename Rename.succ := by
  obtain ⟨e', he⟩ := Exp.unshiftLockIns e (LockIns.here)
  exact ⟨e', he⟩

end CoreCapybara
