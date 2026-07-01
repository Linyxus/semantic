import Semantic.CoreCapybara.Compilation.LockKernel
open CoreCapybara
namespace Compilation

/-!
# Peak-list combinatorics (substitution-independent)

Generic facts about `peakList`/`peakCvars`/`peakSepCtx`/`SepCtx.HasTwoDistinct` that
don't involve any substitution — used by both `SubtypCompile.lean` (the same-context
`CapySubcapt`-based lock transport) and, via `OpenCVarSubtyp.lean`'s own copies, the
substitution-based bridge.  Kept in a dedicated `PC` namespace (rather than reusing
the names `OpenCVarSubtyp.lean` independently defines) to avoid redeclaration once
`OpenCVarSubtyp.lean` transitively imports this file through `SubtypCompile.lean`.
-/

namespace PC

theorem dedup_nodup {α : Type} [DecidableEq α] (l : List α) : (dedup l).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    simp only [dedup]
    split
    · exact ih
    · rename_i hnotin; exact List.nodup_cons.mpr ⟨hnotin, ih⟩

theorem peakCvars_nodup {s : Sig} (P : CapyPeakSet s) : (peakCvars P).Nodup :=
  dedup_nodup _

theorem peakPseudos_nodup {s : Sig} (P : CapyPeakSet s) : (peakPseudos P).Nodup :=
  dedup_nodup _

theorem peakList_nodup {s : Sig} (P : CapyPeakSet s) : (peakList P).Nodup := by
  refine List.nodup_append.mpr ⟨(peakCvars_nodup P).map (fun _ _ h => Peak.cvar.inj h),
    (peakPseudos_nodup P).map (fun _ _ h => Peak.pseudo.inj h), ?_⟩
  intro p hpc
  obtain ⟨c, _, hc⟩ := List.mem_map.mp hpc
  subst hc
  simp [List.mem_map]

theorem mem_peakCvars_of_cvar_mem {s : Sig} {P : CapyPeakSet s} {d : BVar s .cvar}
    (h : Peak.cvar d ∈ peakList P) : d ∈ peakCvars P := by
  simp only [peakList, List.mem_append, List.mem_map] at h
  rcases h with ⟨d', hd', he⟩ | ⟨D, _, he⟩
  · exact Peak.cvar.inj he ▸ hd'
  · exact absurd he (by simp)

theorem mem_peakPseudos_of_pseudo_mem {s : Sig} {P : CapyPeakSet s} {D : CapyCaptureSet s}
    (h : Peak.pseudo D ∈ peakList P) : D ∈ peakPseudos P := by
  simp only [peakList, List.mem_append, List.mem_map] at h
  rcases h with ⟨d', _, he⟩ | ⟨D', hD', he⟩
  · exact absurd he (by simp)
  · exact Peak.pseudo.inj he ▸ hD'

theorem cvar_mem_peakList {s : Sig} {P : CapyPeakSet s} {d : BVar s .cvar}
    (h : d ∈ peakCvars P) : Peak.cvar d ∈ peakList P :=
  List.mem_append_left _ (List.mem_map_of_mem h)

theorem pseudo_mem_peakList {s : Sig} {P : CapyPeakSet s} {D : CapyCaptureSet s}
    (h : D ∈ peakPseudos P) : Peak.pseudo D ∈ peakList P :=
  List.mem_append_right _ (List.mem_map_of_mem h)

theorem peakPseudos_go_nil_of_noPseudoPeak {s : Sig} {cs : CapyCaptureSet s}
    (h : cs.NoPseudoPeak) : peakPseudos.go cs = [] := by
  induction h with
  | empty => rfl
  | cvar => rfl
  | var => rfl
  | union _ _ ih1 ih2 => simp only [peakPseudos.go, ih1, ih2, List.append_nil]

theorem pseudo_not_mem_peakList_of_noPseudoPeak {s : Sig} {P : CapyPeakSet s}
    {D : CapyCaptureSet s} (hnp : P.cs.NoPseudoPeak)
    (h : Peak.pseudo D ∈ peakList P) : False := by
  have hD := mem_peakPseudos_of_pseudo_mem h
  simp only [peakPseudos] at hD
  rw [peakPseudos_go_nil_of_noPseudoPeak hnp] at hD
  simp [dedup] at hD

theorem accessedAt_go_subset {s : Sig} {c : BVar s .cvar} {a : Access} (cs : CapyCaptureSet s)
    (h : a ∈ accessedAt.go c cs) : (CapyCaptureSet.cvar a c) ⊆ cs := by
  induction cs with
  | empty => simp only [accessedAt.go] at h; cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [accessedAt.go, List.mem_append] at h
    rcases h with h1 | h2
    · exact .union_right_left (ih1 h1)
    · exact .union_right_right (ih2 h2)
  | cvar a' c' =>
    simp only [accessedAt.go] at h
    split at h
    · rename_i hcc; subst hcc; simp only [List.mem_singleton] at h; subst h; exact .refl
    · simp only [List.not_mem_nil] at h
  | var a' x => simp only [accessedAt.go] at h; cases h
  | pseudo_peak _ _ => simp only [accessedAt.go] at h; cases h

theorem accessedAt_go_mem {s : Sig} {c : BVar s .cvar} {a : Access} (cs : CapyCaptureSet s)
    (h : (CapyCaptureSet.cvar a c) ⊆ cs) : a ∈ accessedAt.go c cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [accessedAt.go, List.mem_append]
    cases h with
    | union_right_left h1 => exact Or.inl (ih1 h1)
    | union_right_right h2 => exact Or.inr (ih2 h2)
  | cvar a' c' =>
    cases h
    simp [accessedAt.go]
  | var a' x => cases h
  | pseudo_peak _ _ => cases h

theorem mem_dedup {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : a ∈ dedup l := by
  induction l with
  | nil => cases h
  | cons b bs ih =>
    simp only [dedup]
    rcases List.mem_cons.mp h with rfl | hmem
    · split
      · rename_i hb; exact hb
      · exact List.mem_cons_self
    · have hd := ih hmem
      split
      · exact hd
      · exact List.mem_cons_of_mem _ hd

theorem mem_dedup_inv {α : Type} [DecidableEq α] {a : α} {l : List α} (h : a ∈ dedup l) :
    a ∈ l := by
  induction l with
  | nil => exact h
  | cons b bs ih =>
    simp only [dedup] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hm)

theorem peakCvars_go_occ {s : Sig} {c : BVar s .cvar} :
    ∀ {cs : CapyCaptureSet s}, c ∈ peakCvars.go cs → ∃ a, (CapyCaptureSet.cvar a c) ⊆ cs := by
  intro cs
  induction cs with
  | empty => intro h; simp only [peakCvars.go, List.not_mem_nil] at h
  | union cs1 cs2 ih1 ih2 =>
    intro h
    simp only [peakCvars.go, List.mem_append] at h
    rcases h with h1 | h2
    · obtain ⟨a, ha⟩ := ih1 h1; exact ⟨a, CapyCaptureSet.Subset.union_right_left ha⟩
    · obtain ⟨a, ha⟩ := ih2 h2; exact ⟨a, CapyCaptureSet.Subset.union_right_right ha⟩
  | cvar a' c' =>
    intro h; simp only [peakCvars.go, List.mem_singleton] at h
    subst h; exact ⟨a', CapyCaptureSet.Subset.refl⟩
  | var a' x => intro h; simp only [peakCvars.go, List.not_mem_nil] at h
  | pseudo_peak _ _ => intro h; simp only [peakCvars.go, List.not_mem_nil] at h

theorem peakCvars_occ {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar}
    (h : c ∈ peakCvars P) : ∃ a, (CapyCaptureSet.cvar a c) ⊆ P.cs :=
  peakCvars_go_occ (mem_dedup_inv (by simpa only [peakCvars] using h))

theorem cvar_subset_peakCvars_go {s : Sig} {c : BVar s .cvar} {a : Access} (cs : CapyCaptureSet s)
    (h : (CapyCaptureSet.cvar a c) ⊆ cs) : c ∈ peakCvars.go cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [peakCvars.go, List.mem_append]
    cases h with
    | union_right_left h1 => exact Or.inl (ih1 h1)
    | union_right_right h2 => exact Or.inr (ih2 h2)
  | cvar a' c' => cases h; simp [peakCvars.go]
  | var a' x => cases h
  | pseudo_peak _ _ => cases h

theorem cvar_mem_peakCvars {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} {a : Access}
    (h : (CapyCaptureSet.cvar a c) ⊆ P.cs) : c ∈ peakCvars P := by
  simp only [peakCvars]
  exact mem_dedup (cvar_subset_peakCvars_go P.cs h)

theorem cvar_subset_peakItem {s : Sig} {P : CapyPeakSet s} {c : BVar s .cvar} {a : Access}
    (h : (CapyCaptureSet.cvar a c) ⊆ P.cs) : (CapyCaptureSet.cvar a c) ⊆ peakItem P c := by
  simp only [peakItem]
  have hmem : a ∈ accessedAt P c := by simpa only [accessedAt] using accessedAt_go_mem _ h
  simp only [accessedAt] at hmem ⊢
  generalize accessedAt.go c P.cs = l at hmem
  induction l with
  | nil => cases hmem
  | cons a' l' ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact .union_right_left .refl
    · exact .union_right_right (ih hmem')

theorem pseudo_subset_peakPseudos_go {s : Sig} {C : CapyCaptureSet s} (cs : CapyCaptureSet s)
    (h : (CapyCaptureSet.pseudo_peak C) ⊆ cs) : C.modeErase ∈ peakPseudos.go cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [peakPseudos.go, List.mem_append]
    cases h with
    | union_right_left h1 => exact Or.inl (ih1 h1)
    | union_right_right h2 => exact Or.inr (ih2 h2)
  | cvar a c => cases h
  | var a x => cases h
  | pseudo_peak C' ih => cases h; simp [peakPseudos.go]

theorem pseudoBase_mem_peakPseudos {s : Sig} {P : CapyPeakSet s} {C : CapyCaptureSet s}
    (h : (CapyCaptureSet.pseudo_peak C) ⊆ P.cs) : C.modeErase ∈ peakPseudos P :=
  mem_dedup (pseudo_subset_peakPseudos_go P.cs h)

theorem peakPseudos_go_occ {s : Sig} {D : CapyCaptureSet s} :
    ∀ {cs : CapyCaptureSet s}, D ∈ peakPseudos.go cs →
      ∃ C, (CapyCaptureSet.pseudo_peak C) ⊆ cs ∧ C.modeErase = D := by
  intro cs
  induction cs with
  | empty => intro h; simp only [peakPseudos.go, List.not_mem_nil] at h
  | union cs1 cs2 ih1 ih2 =>
    intro h
    simp only [peakPseudos.go, List.mem_append] at h
    rcases h with h1 | h2
    · obtain ⟨C, hC, hCm⟩ := ih1 h1; exact ⟨C, CapyCaptureSet.Subset.union_right_left hC, hCm⟩
    · obtain ⟨C, hC, hCm⟩ := ih2 h2; exact ⟨C, CapyCaptureSet.Subset.union_right_right hC, hCm⟩
  | cvar a c => intro h; simp only [peakPseudos.go, List.not_mem_nil] at h
  | var a x => intro h; simp only [peakPseudos.go, List.not_mem_nil] at h
  | pseudo_peak C _ =>
    intro h; simp only [peakPseudos.go, List.mem_singleton] at h
    exact ⟨C, CapyCaptureSet.Subset.refl, h.symm⟩

theorem peakPseudos_occ {s : Sig} {P : CapyPeakSet s} {D : CapyCaptureSet s}
    (h : D ∈ peakPseudos P) : ∃ C, (CapyCaptureSet.pseudo_peak C) ⊆ P.cs ∧ C.modeErase = D :=
  peakPseudos_go_occ (mem_dedup_inv (by simpa only [peakPseudos] using h))

theorem pseudo_subset_pseudoItem_go {s : Sig} {C D : CapyCaptureSet s} (hD : C.modeErase = D)
    (cs : CapyCaptureSet s) (h : (CapyCaptureSet.pseudo_peak C) ⊆ cs) :
    (CapyCaptureSet.pseudo_peak C) ⊆ pseudoItem.go D cs := by
  induction cs with
  | empty => cases h
  | union cs1 cs2 ih1 ih2 =>
    simp only [pseudoItem.go]
    cases h with
    | union_right_left h1 => exact .union_right_left (ih1 h1)
    | union_right_right h2 => exact .union_right_right (ih2 h2)
  | cvar a c => cases h
  | var a x => cases h
  | pseudo_peak C' ih =>
    cases h
    simp only [pseudoItem.go]
    rw [if_pos hD]
    exact CapyCaptureSet.Subset.refl

theorem pseudo_subset_pseudoItem {s : Sig} {P : CapyPeakSet s} {C : CapyCaptureSet s}
    (h : (CapyCaptureSet.pseudo_peak C) ⊆ P.cs) :
    (CapyCaptureSet.pseudo_peak C) ⊆ pseudoItem P (C.modeErase) := by
  simp only [pseudoItem]
  exact pseudo_subset_pseudoItem_go rfl P.cs h

theorem hasTwoDistinct_foldl_mono {α : Type} {s : Sig} {g : α → CaptureSet s}
    {C1 C2 : CaptureSet s} (L : List α) :
    ∀ {acc : SepCtx s}, SepCtx.HasTwoDistinct acc C1 C2 →
      SepCtx.HasTwoDistinct (L.foldl (fun K c => .cons K (g c)) acc) C1 C2 := by
  induction L with
  | nil => intro acc h; exact h
  | cons c L' ih => intro acc h; exact ih h.there

theorem hasTwoDistinct_foldl_acc {α : Type} {s : Sig} {g : α → CaptureSet s}
    {C1 : CaptureSet s} {a : α} (L : List α) :
    a ∈ L → ∀ {acc : SepCtx s}, SepCtx.Has acc C1 →
      SepCtx.HasTwoDistinct (L.foldl (fun K c => .cons K (g c)) acc) C1 (g a) := by
  induction L with
  | nil => intro ha; simp at ha
  | cons c L' ih =>
    intro ha acc hC1
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact hasTwoDistinct_foldl_mono L' (SepCtx.HasTwoDistinct.here_there hC1).symm
    · exact ih hmem hC1.there

theorem hasTwoDistinct_foldl {α : Type} {s : Sig} {g : α → CaptureSet s} {a b : α}
    (L : List α) :
    a ∈ L → b ∈ L → a ≠ b →
    ∀ {acc : SepCtx s},
      SepCtx.HasTwoDistinct (L.foldl (fun K c => .cons K (g c)) acc) (g a) (g b) := by
  induction L with
  | nil => intro ha _ _; simp at ha
  | cons c L' ih =>
    intro ha hb hab acc
    rcases List.mem_cons.mp ha with rfl | haL'
    · rcases List.mem_cons.mp hb with rfl | hbL'
      · exact absurd rfl hab
      · exact hasTwoDistinct_foldl_acc L' hbL' SepCtx.Has.here
    · rcases List.mem_cons.mp hb with rfl | hbL'
      · exact (hasTwoDistinct_foldl_acc L' haL' SepCtx.Has.here).symm
      · exact ih haL' hbL' hab

theorem peakSepCtx_hasTwoDistinct_of {s1 s2 : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2} {p1 p2 : Peak s1}
    (hc1 : p1 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    (hc2 : p2 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    (hne : p1 ≠ p2) :
    SepCtx.HasTwoDistinct (peakSepCtx Γ P sc)
      (CapyCaptureSet.compile (peakKeyItem P p1) sc)
      (CapyCaptureSet.compile (peakKeyItem P p2) sc) := by
  simp only [peakSepCtx]
  exact hasTwoDistinct_foldl
    (g := fun p => CapyCaptureSet.compile (peakKeyItem P p) sc)
    ((peakList P).filter (fun p => decide (Peak.IsStable Γ p))) hc1 hc2 hne

theorem has_foldl_empty_inv {α : Type} {s : Sig} {g : α → CaptureSet s} (L : List α) :
    ∀ {acc : SepCtx s} {C : CaptureSet s},
      SepCtx.Has (L.foldl (fun K c => SepCtx.cons K (g c)) acc) C →
      SepCtx.Has acc C ∨ ∃ c ∈ L, C = g c := by
  induction L with
  | nil => intro acc C h; exact Or.inl h
  | cons c L' ih =>
    intro acc C h
    rw [List.foldl_cons] at h
    rcases ih h with h' | ⟨c', hc', he⟩
    · cases h' with
      | here => exact Or.inr ⟨c, List.mem_cons_self, rfl⟩
      | there h'' => exact Or.inl h''
    · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', he⟩

theorem foldl_empty_eq_cons_inv {α : Type} {s : Sig} {g : α → CaptureSet s} {L : List α}
    {K0 : SepCtx s} {C : CaptureSet s}
    (h : L.foldl (fun K c => SepCtx.cons K (g c)) SepCtx.empty = SepCtx.cons K0 C) :
    ∃ (L0 : List α) (c' : α), L = L0 ++ [c'] ∧
      K0 = L0.foldl (fun K c => SepCtx.cons K (g c)) SepCtx.empty ∧ C = g c' := by
  rcases List.eq_nil_or_concat L with rfl | ⟨L0, c', rfl⟩
  · rw [List.foldl_nil] at h; cases h
  · rw [List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    injection h with hK hC
    refine ⟨L0, c', ?_, hK.symm, hC.symm⟩
    rw [List.concat_eq_append]

theorem hasTwoDistinct_foldl_nodup {α : Type} {s : Sig} {g : α → CaptureSet s}
    {K : SepCtx s} {C1 C2 : CaptureSet s} (h : SepCtx.HasTwoDistinct K C1 C2) :
    ∀ (L : List α), L.Nodup → K = L.foldl (fun K c => SepCtx.cons K (g c)) SepCtx.empty →
      ∃ c1 ∈ L, ∃ c2 ∈ L, c1 ≠ c2 ∧
        ((C1 = g c1 ∧ C2 = g c2) ∨ (C1 = g c2 ∧ C2 = g c1)) := by
  induction h with
  | @here_there K0 C2v C1v hHas =>
    intro L hnd hK
    obtain ⟨L0, c', hL, hK0, hC1⟩ := foldl_empty_eq_cons_inv hK.symm
    subst hL
    have hnotin : c' ∉ L0 := by
      have hdisj := (List.nodup_append.mp hnd).2.2
      intro hc; exact hdisj c' hc c' (by simp) rfl
    rcases has_foldl_empty_inv L0 (hK0 ▸ hHas) with hemp | ⟨c2, hc2, he2⟩
    · cases hemp
    · refine ⟨c', List.mem_append_right _ (by simp), c2, List.mem_append_left _ hc2, ?_,
        Or.inl ⟨hC1, he2⟩⟩
      intro heq; subst heq; exact hnotin hc2
  | @there K0 C1v C2v Cv _ ih =>
    intro L hnd hK
    obtain ⟨L0, c', hL, hK0, _⟩ := foldl_empty_eq_cons_inv hK.symm
    subst hL
    have hnd0 : L0.Nodup := (List.nodup_append.mp hnd).1
    obtain ⟨c1, hc1, c2, hc2, hne, hdisj⟩ := ih L0 hnd0 hK0
    exact ⟨c1, List.mem_append_left _ hc1, c2, List.mem_append_left _ hc2, hne, hdisj⟩
  | @symm K0 C1v C2v _ ih =>
    intro L hnd hK
    obtain ⟨c1, hc1, c2, hc2, hne, hdisj⟩ := ih L hnd hK
    refine ⟨c1, hc1, c2, hc2, hne, ?_⟩
    rcases hdisj with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inr ⟨hb, ha⟩
    · exact Or.inl ⟨hb, ha⟩

theorem peakSepCtx_hasTwoDistinct_ne {s1 s2 : Sig} {Γ : CapyCtx s1} {P : CapyPeakSet s1}
    {sc : SrcCtx s1 s2} {C1 C2 : CaptureSet s2}
    (h : SepCtx.HasTwoDistinct (peakSepCtx Γ P sc) C1 C2) :
    ∃ p1 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)),
      ∃ p2 ∈ (peakList P).filter (fun p => decide (Peak.IsStable Γ p)), p1 ≠ p2 ∧
      ((C1 = CapyCaptureSet.compile (peakKeyItem P p1) sc ∧
          C2 = CapyCaptureSet.compile (peakKeyItem P p2) sc) ∨
       (C1 = CapyCaptureSet.compile (peakKeyItem P p2) sc ∧
          C2 = CapyCaptureSet.compile (peakKeyItem P p1) sc)) :=
  hasTwoDistinct_foldl_nodup (g := fun p => CapyCaptureSet.compile (peakKeyItem P p) sc) h
    ((peakList P).filter (fun p => decide (Peak.IsStable Γ p)))
    ((peakList_nodup P).filter _) rfl

end PC
end Compilation
