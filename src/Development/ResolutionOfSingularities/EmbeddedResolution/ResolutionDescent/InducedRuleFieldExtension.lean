module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldExtensionEtaleCover
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemoval
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem notMem_support_comap_top {A C : Scheme.{u}} (h : A ⟶ C) (x : ↥A) :
    x ∉ ((⊤ : C.IdealSheafData).comap h).support := by
  rw [Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.support_top]
  intro hx
  have hx' : x ∈ ((⊥ : TopologicalSpace.Closeds ↥A) : Set ↥A) := hx
  simp at hx'

theorem center_ne_top_of_isPullbackSequenceOfBlowups_id {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (h : IsPullbackBlowupSequence (𝟙 X) s s) :
    ∀ i : ℕ, i < s.length → s.center i ≠ ⊤ := by
  obtain ⟨r, _e, _hlt, hmono, htop, hsupp, -⟩ := h
  have hgeid : ∀ i : ℕ, i ≤ s.length → i ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have h1 : r n < r (n + 1) := hmono n (n + 1) hn (Nat.lt_succ_self n)
      have h2 : n ≤ r n := ih (Nat.le_of_succ_le hn)
      omega
  have hleid : ∀ d i : ℕ, i + d = s.length → r i + d ≤ s.length := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hii : i = s.length := by omega
      subst hii
      rw [htop]
      omega
    | succ m ih =>
      intro i hi
      have hi1 : (i + 1) + m = s.length := by omega
      have h2 := ih (i + 1) hi1
      have h3 : r i < r (i + 1) := hmono i (i + 1) (by omega) (Nat.lt_succ_self i)
      omega
  have hrid : ∀ i : ℕ, i ≤ s.length → r i = i := by
    intro i hi
    have h1 := hgeid i hi
    have h2 := hleid (s.length - i) i (by omega)
    omega
  intro i hi hc
  obtain ⟨x, hx⟩ := (hsupp i hi).mpr ⟨i, hi, hrid i hi.le⟩
  rw [hc] at hx
  exact notMem_support_comap_top _ x hx

theorem AffineResolutionRule.center_ne_top (B : AffineResolutionRule.{u}) (hB : IsCompatibleWithOpenImmersions B)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] :
    ∀ i : ℕ, i < (B k Y p).length → (B k Y p).center i ≠ ⊤ :=
  center_ne_top_of_isPullbackSequenceOfBlowups_id (B k Y p) (hB k Y Y p p (𝟙 Y) (Category.id_comp p))

theorem inducedRuleCompatibleWithFieldExtension (B : AffineResolutionRule.{u}) : InducedRuleCompatibleWithFieldExtension B := by
  intro hoi hfe F hF k _ _ X f _ _ _ K _ _ _ _
  obtain ⟨W, c, g, hWaff, hWred, hqlft, hqqc, hcet, hcsur, hYaff, hYred, hglft, hgqc, hget,
    hgsur, hgstruct, hgproj⟩ := exists_etale_surjective_affine_cover_baseChange X f K
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hcet
  have := hcsur
  have := hYaff
  have := hYred
  have := hglft
  have := hgqc
  have := hget
  have := hgsur
  have h0 : IsStrictPullbackBlowupSeq (baseChangeProjection f K)
      ((F k X f).baseChange (baseChangeProjection f K)) (F k X f) :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hw : IsStrictPullbackBlowupSeq g
      (((F k X f).baseChange (baseChangeProjection f K)).baseChange g)
      ((F k X f).baseChange (baseChangeProjection f K)) :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hcomp := hw.comp h0
  rw [hgproj] at hcomp
  have htW : IsStrictPullbackBlowupSeq c (B k W (c ≫ f)) (F k X f) :=
    hF k X f W (c ≫ f) c rfl AlgebraicGeometry.Surjective.surj
  have htK : IsStrictPullbackBlowupSeq (baseChangeProjection (c ≫ f) K)
      (B K (baseChange (c ≫ f) K) (baseChangeToSpec (c ≫ f) K)) (B k W (c ≫ f)) :=
    hfe k W (c ≫ f) K
  have hEqw := hcomp.isomorphic (htK.comp htW)
  have hntop := AffineResolutionRule.center_ne_top B hoi K (baseChange (c ≫ f) K)
      (baseChangeToSpec (c ≫ f) K)
  have local0 {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a ≤ b)
      (h' : a = b) : s.transitionMap h = eqToHom (congrArg s.schemeAt h'.symm) := by
    subst h'
    rw [s.transitionMap_self h, eqToHom_refl]

  have local1 {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b a' b' : ℕ}
      (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
      eqToHom (congrArg s.schemeAt hb) ≫ s.transitionMap h' = s.transitionMap h ≫ eqToHom (congrArg s.schemeAt ha) := by
    subst ha
    subst hb
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

  have local2 {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
      eqToHom (congrArg s.schemeAt h) ≫ s.projectionToBase b = s.projectionToBase a := by
    subst h
    rw [eqToHom_refl, Category.id_comp]

  have local3 {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
      (s.center b).comap (eqToHom (congrArg s.schemeAt h)) = s.center a := by
    subst h
    simp

  have local4 {X : Scheme.{u}} (t : SequenceOfBlowups X)
      (h : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) : t.withoutIsoBlowups.Isomorphic t := by
    have hnext : ∀ a : ℕ, t.nextNontrivialIndex a = a := by
      intro a
      refine le_antisymm (t.nextNontrivialIndex_le le_rfl ?_) (t.le_nextNontrivialIndex a)
      by_cases ha : a < t.length
      · exact Or.inl (h a ha)
      · exact Or.inr (by omega)
    have hret : ∀ j : ℕ, t.nontrivialIndex j = j := by
      intro j
      induction j with
      | zero => rw [t.nontrivialIndex_zero, hnext]
      | succ j ih => rw [t.nontrivialIndex_succ, hnext, ih]
    have hplen : t.withoutIsoBlowups.length = t.length := by
      have h2 := t.nontrivialIndex_lengthWithoutIsoBlowups
      rw [hret] at h2
      exact h2
    have h1 : (eqToIso (congrArg t.schemeAt (hret 0))).hom ≫ t.isoZero.hom = t.withoutIsoBlowups.isoZero.hom := by
      rw [t.withoutIsoBlowups_isoObjZero, t.objNontrivialIndexZeroIso_hom, t.projectionToBase_def,
        local0 t _ (hret 0).symm]
      rfl
    have h2 : ∀ i : ℕ, i < t.withoutIsoBlowups.length →
        (eqToIso (congrArg t.schemeAt (hret (i + 1)))).hom ≫ t.transitionMapSucc i
          = t.withoutIsoBlowups.transitionMapSucc i ≫ (eqToIso (congrArg t.schemeAt (hret i))).hom := by
      intro i _
      rw [t.withoutIsoBlowups_blowupMorphism, t.blowupMorphism_eq_transitionMap]
      exact local1 t (hret i) (hret (i + 1)) _ _
    have h3 : ∀ i : ℕ, i < t.withoutIsoBlowups.length →
        (t.center i).comap (eqToIso (congrArg t.schemeAt (hret i))).hom = t.withoutIsoBlowups.center i := by
      intro i _
      exact local3 t (hret i)
    unfold SequenceOfBlowups.Isomorphic
    exact ⟨hplen, fun i _ => eqToIso (congrArg t.schemeAt (hret i)), h1, h2, h3⟩


  have local5 {P Y X Z X' Z' : Scheme.{u}}
      {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
      (h : IsPullback fst snd f g) (hX : X = X') (hZ : Z = Z') {f' : X' ⟶ Z'}
      (hf : eqToHom hX ≫ f' = f ≫ eqToHom hZ) :
      IsPullback (fst ≫ eqToHom hX) snd f' (g ≫ eqToHom hZ) := by
    subst hX
    subst hZ
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hf ⊢
    rw [hf]
    exact h

  have local6 {X' X : Scheme.{u}} (t : SequenceOfBlowups X')
      (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) (f : t.schemeAt a ⟶ s.schemeAt a)
      (hf : t.center a = (s.center a).comap f) :
      t.center a = (s.center b).comap (f ≫ eqToHom (congrArg s.schemeAt hab)) := by
    subst hab
    simp only [eqToHom_refl, Category.comp_id]
    exact hf

  have local7 {X' X : Scheme.{u}} {g : X' ⟶ X}
      [AlgebraicGeometry.Surjective g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
      (h : IsStrictPullbackBlowupSeq g t s) :
      IsStrictPullbackBlowupSeq g t.withoutIsoBlowups s.withoutIsoBlowups := by
    have hiff : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤) :=
      fun i hi => h.center_eq_top_iff i hi
    have hlen : t.length = s.length := h.length_eq
    have hret : ∀ j : ℕ, t.nontrivialIndex j = s.nontrivialIndex j := SequenceOfBlowups.nontrivialIndex_congr t s hlen hiff
    have hplen : t.lengthWithoutIsoBlowups = s.lengthWithoutIsoBlowups := SequenceOfBlowups.lengthWithoutIsoBlowups_congr t s hlen hiff
    unfold IsStrictPullbackBlowupSeq at h ⊢
    obtain ⟨-, σ, hzero, hstep, hcen⟩ := h
    have hstruct := isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hzero hstep
    have hdown := isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep
    have h1 : (σ (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (Nat.zero_le _)) ≫
          eqToHom (congrArg s.schemeAt (hret 0))) ≫ s.withoutIsoBlowups.isoZero.hom
        = t.withoutIsoBlowups.isoZero.hom ≫ g := by
      rw [s.withoutIsoBlowups_isoObjZero, t.withoutIsoBlowups_isoObjZero, s.objNontrivialIndexZeroIso_hom, t.objNontrivialIndexZeroIso_hom,
        Category.assoc, local2 s (hret 0)]
      exact (hstruct (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (Nat.zero_le _))).w
    have h2 : ∀ j : ℕ, ∀ hj : j < t.withoutIsoBlowups.length,
        IsPullback
          (σ (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_le_length hj) ≫
            eqToHom (congrArg s.schemeAt (hret (j + 1))))
          (t.withoutIsoBlowups.transitionMapSucc j) (s.withoutIsoBlowups.transitionMapSucc j)
          (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
            eqToHom (congrArg s.schemeAt (hret j))) := by
      intro j hj
      rw [t.withoutIsoBlowups_blowupMorphism, s.withoutIsoBlowups_blowupMorphism]
      exact local5
        (hdown (t.nontrivialIndex j) (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_monotone (Nat.le_succ j))
          (t.nontrivialIndex_le_length hj))
        (congrArg s.schemeAt (hret (j + 1))) (congrArg s.schemeAt (hret j))
        (local1 s (hret j) (hret (j + 1))
          (t.nontrivialIndex_monotone (Nat.le_succ j)) (s.nontrivialIndex_monotone (Nat.le_succ j)))
    have h3 : ∀ j : ℕ, ∀ hj : j < t.withoutIsoBlowups.length,
        t.withoutIsoBlowups.center j = (s.withoutIsoBlowups.center j).comap
          (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
            eqToHom (congrArg s.schemeAt (hret j))) := by
      intro j hj
      exact local6 t s (hret j)
        (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)))
        (hcen (t.nontrivialIndex j) (t.nontrivialIndex_lt_length hj))
    exact ⟨hplen, fun j hj => σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length hj) ≫
      eqToHom (congrArg s.schemeAt (hret j)), h1, h2, h3⟩
  have local9 {A : Scheme.{u}} (I : A.IdealSheafData) :
      (∃ x, x ∈ I.support) ↔ I ≠ ⊤ := by
    constructor
    · rintro ⟨x, hx⟩ rfl
      rw [Scheme.IdealSheafData.support_top] at hx
      exact hx
    · intro hne
      by_contra hc
      push Not at hc
      exact hne ((Scheme.IdealSheafData.support_eq_bot_iff I).mp
        (SetLike.ext fun x => iff_of_false (hc x) (fun hmem => hmem)))

  have local10 {A B : Scheme.{u}} (e : A ≅ B) (J : B.IdealSheafData) :
      J.comap e.hom = ⊤ ↔ J = ⊤ := by
    constructor
    · intro hJ
      have h1 : (J.comap e.hom).comap e.inv = J := by
        rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
      rw [← h1, hJ]
      simp
    · rintro rfl
      simp





  have local11 {X : Scheme.{u}} (s : SequenceOfBlowups X) (j : ℕ) :
      s.withoutIsoBlowups.projectionToBase j = s.projectionToBase (s.nontrivialIndex j) := by
    have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
    rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.withoutIsoBlowups_transitionMap, h0]
    exact s.transitionMap_comp_projectionToBase (s.nontrivialIndex_monotone (Nat.zero_le j))

  have local12 {X : Scheme.{u}} (s : SequenceOfBlowups X) {i : ℕ} (hi : i < s.length)
      (h : s.center i ≠ ⊤) :
      ∃ j, j < s.lengthWithoutIsoBlowups ∧ s.nontrivialIndex j = i := by
    have hex : ∃ n, i < s.nontrivialIndex n :=
      ⟨s.lengthWithoutIsoBlowups, by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi⟩
    obtain ⟨n, hn1, hn2, hn3⟩ :
        ∃ n, i < s.nontrivialIndex n ∧ (∀ m, m < n → ¬ (i < s.nontrivialIndex m)) ∧ n ≤ s.lengthWithoutIsoBlowups :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm,
        Nat.find_le (by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi)⟩
    cases n with
    | zero => exact absurd (s.center_eq_top_of_lt_nontrivialIndex_zero hn1) h
    | succ m =>
        have hmi : s.nontrivialIndex m ≤ i := not_lt.mp (hn2 m (Nat.lt_succ_self m))
        refine ⟨m, by omega, ?_⟩
        rcases eq_or_lt_of_le hmi with heq | hlt
        · exact heq
        · exact absurd (s.center_eq_top_of_nontrivialIndex_lt hlt hn1) h
  have local8 {X' X : Scheme.{u}} {φ : X' ⟶ X}
      {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
      (h : IsStrictPullbackBlowupSeq φ t s) :
      IsPullbackBlowupSequence φ t.withoutIsoBlowups s := by
    obtain ⟨hlen, σ, hzero, hstep, hcen⟩ := h
    have hstructPB : ∀ (i : ℕ) (hi : i ≤ t.length),
        IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) φ :=
      isPullback_projectionToBase_of_isPullback_blowupMorphism φ t s t.length σ hzero hstep
    have hdownPB : ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ t.length),
        IsPullback (σ b hb) (t.transitionMap hab) (s.transitionMap hab) (σ a (hab.trans hb)) :=
      isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep
    obtain ⟨e, he1, he2⟩ :
        ∃ e : ∀ i : ℕ, i ≤ t.withoutIsoBlowups.length →
            (t.withoutIsoBlowups.schemeAt i ≅ Limits.pullback φ (s.projectionToBase (t.nontrivialIndex i))),
          (∀ (i : ℕ) (hi : i ≤ t.withoutIsoBlowups.length),
              (e i hi).hom ≫ Limits.pullback.fst φ (s.projectionToBase (t.nontrivialIndex i))
                = t.projectionToBase (t.nontrivialIndex i)) ∧
          (∀ (i : ℕ) (hi : i ≤ t.withoutIsoBlowups.length),
              (e i hi).hom ≫ Limits.pullback.snd φ (s.projectionToBase (t.nontrivialIndex i))
                = σ (t.nontrivialIndex i)
                    (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))) := by
      refine ⟨fun i hi => ((hstructPB (t.nontrivialIndex i)
          (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback, ?_, ?_⟩
      · intro i hi
        exact ((hstructPB (t.nontrivialIndex i)
          (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback_hom_fst
      · intro i hi
        exact ((hstructPB (t.nontrivialIndex i)
          (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback_hom_snd
    refine ⟨t.nontrivialIndex, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have h1 := t.nontrivialIndex_lt_length hi
      omega
    · intro i j _ hij
      exact t.nontrivialIndex_strictMono hij
    · exact t.nontrivialIndex_lengthWithoutIsoBlowups.trans hlen
    · intro i hi
      have hi' : i < t.length := by omega
      have hcomap : ((s.center i).comap (Limits.pullback.snd φ (s.projectionToBase i))).comap
          (((hstructPB i hi'.le).flip).isoPullback.hom) = t.center i := by
        rw [← Scheme.IdealSheafData.comap_comp,
          ((hstructPB i hi'.le).flip).isoPullback_hom_snd]
        exact (hcen i hi').symm
      rw [local9]
      constructor
      · intro hne
        refine local12 t hi' ?_
        intro htop
        exact hne ((local10 _ _).mp (hcomap.trans htop))
      · rintro ⟨j, hj, rfl⟩
        intro htop
        refine t.center_nontrivialIndex_ne_top hj ?_
        rw [← hcomap, htop]
        simp
    · intro i hi
      rw [he1 i hi, local11 t]
    · intro i hi hr
      have hbi : t.nontrivialIndex (i + 1) ≤ t.length :=
        t.nontrivialIndex_le_length (show i + 1 ≤ t.lengthWithoutIsoBlowups from hi)
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc, he1, s.pullbackTransitionMap_fst, he1, t.withoutIsoBlowups_blowupMorphism i]
        exact t.transitionMap_comp_projectionToBase (t.nontrivialIndex_monotone (Nat.le_succ i))
      · rw [Category.assoc, Category.assoc, he2, s.pullbackTransitionMap_snd, ← Category.assoc, he2,
          t.withoutIsoBlowups_blowupMorphism i]
        exact (hdownPB (t.nontrivialIndex i) (t.nontrivialIndex (i + 1))
          (t.nontrivialIndex_monotone (Nat.le_succ i)) hbi).w.symm
    · intro i hi
      rw [he2 i hi.le]
      exact hcen (t.nontrivialIndex i) (t.nontrivialIndex_lt_length hi)
  have hid : ∀ {Z : Scheme.{u}} {s t : SequenceOfBlowups Z},
      s.Isomorphic t → IsStrictPullbackBlowupSeq (𝟙 Z) s t := by
    intro Z s t h
    unfold SequenceOfBlowups.Isomorphic at h
    unfold IsStrictPullbackBlowupSeq
    obtain ⟨hlen, e, hzero, hstep, hcen⟩ := h
    refine ⟨hlen, fun i hi => (e i hi).hom, ?_, ?_, ?_⟩
    · simpa using hzero
    · intro i hi
      exact IsPullback.of_horiz_isIso ⟨hstep i hi⟩
    · intro i hi
      exact (hcen i hi).symm
  have hEq := ((local7 (hid hEqw)).isomorphic
    (hid (SequenceOfBlowups.isomorphic_refl _))).trans (local4 _ hntop)
  have h₂ : IsStrictPullbackBlowupSeq g (B K (baseChange (c ≫ f) K) (baseChangeToSpec (c ≫ f) K))
      (F K (baseChange f K) (baseChangeToSpec f K)) :=
    hF K (baseChange f K) (baseChangeToSpec f K) (baseChange (c ≫ f) K)
      (baseChangeToSpec (c ≫ f) K) g hgstruct AlgebraicGeometry.Surjective.surj
  have hdesc := IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic (local7 hw) h₂ hEq
  exact (local8 h0).of_isomorphic hdesc

end FunctorialResolution.EmbeddedResolution

end