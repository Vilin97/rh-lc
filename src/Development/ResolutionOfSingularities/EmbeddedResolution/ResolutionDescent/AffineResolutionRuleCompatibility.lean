module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackLocalAmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleOfPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.GraphChartLocalAmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IndependenceOfEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinateCodimensionCriterion
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelection
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EtaleCoverClosedEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothPullbackGraphChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IndependenceOfEmbeddingHypotheses

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem locallyConstCodimImpliesConstantCodim : LocallyConstCodimImpliesConstantCodim.{u} := by
  intro k _ X X' q _ τ _ c h
  exact hasEtaleCoordCodim_of_locally_smooth_over_affineSpace q τ c h

theorem linearEmbeddingsHaveLocallyConstCodim_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth.{u}) :
    LinearEmbeddingsHaveLocallyConstCodim.{u} := by
  intro k _ n m
  exact ⟨hasSmoothCoordCodim_affineSpaceInl hsm k n m, hasSmoothCoordCodim_affineSpaceInrEmbedding hsm k n m⟩

theorem isIndependentOfPresentedEmbedding_embeddedResolutionRule (Alg : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization Alg) (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u})
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    (embeddedResolutionRuleOfPrincipalization Alg hw).IsIndependentOfPresentedEmbedding :=
  isIndependentOfPresentedEmbedding_of_locallyConstCodim Alg hAlg hw hsm hcmp
    locallyConstCodimImpliesConstantCodim (linearEmbeddingsHaveLocallyConstCodim_of_affineSpaceIsSmooth hsm)

end FunctorialResolution.EmbeddedResolution

end
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelectionCompatibility

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isPullbackBlowupSequence_presentedSelection_of_smooth (E : EmbeddedResolutionRule.{u}) (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q [])
    (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (E k V pV (C.sel k V pV)) (E k Y pY (C.sel k Y pY)) := by
  obtain ⟨V'', pV'', c, hV''aff, hV''red, hV''ft, hV''qc, hcet, hcsurj, hcpV,
      ⟨G', f, hG'pres, hfsm, hfcomp, hfpb⟩, ⟨H', g, hH'pres, hgsm, hgcomp, hgpb⟩⟩ :=
    exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth hS hsm k (fun A q hq => hsnc k A q hq)
      Y V pY pV (C.sel k Y pY) (C.pres k Y pY) (C.sel k V pV) (C.pres k V pV) u r hu
  have := hV''aff
  have := hV''red
  have := hV''ft
  have := hV''qc
  have := hcet
  have := hcsurj
  have := hfsm
  have := hgsm
  have : AlgebraicGeometry.Smooth u := AlgebraicGeometry.SmoothOfRelativeDimension.smooth r u
  have : AlgebraicGeometry.Flat u := inferInstance
  have : AlgebraicGeometry.Flat c := inferInstance
  have s1 : IsPullbackBlowupSequence (c ≫ u) (E k V'' pV'' G') (E k Y pY (C.sel k Y pY)) :=
    hsbc k Y V'' pY pV'' (C.sel k Y pY) G' f (c ≫ u) hfcomp hfpb
  have s2 : IsPullbackBlowupSequence c (E k V'' pV'' H') (E k V pV (C.sel k V pV)) :=
    hsbc k V V'' pV pV'' (C.sel k V pV) H' g c hgcomp hgpb
  have heq : (E k V'' pV'' G').Isomorphic (E k V'' pV'' H') :=
    hinv k V'' pV'' G' H' hG'pres.some hH'pres.some
  have s2' : IsStrictPullbackBlowupSeq c (E k V'' pV'' H') (E k V pV (C.sel k V pV)) :=
    s2.isStrictPullback_of_surjective
      (fun i hi => hprop k V pV (C.sel k V pV) i hi)
  have hBu : IsStrictPullbackBlowupSeq u ((E k Y pY (C.sel k Y pY)).baseChange u)
      (E k Y pY (C.sel k Y pY)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (E k Y pY (C.sel k Y pY)) u
  have hB' : IsPullbackBlowupSequence u ((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups
      (E k Y pY (C.sel k Y pY)) := hBu.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have hCc : IsStrictPullbackBlowupSeq c
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c)
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) c
  have hC : IsPullbackBlowupSequence (c ≫ u)
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c)
      (E k Y pY (C.sel k Y pY)) := hB'.comp_isStrictPullbackSequenceOfBlowups hCc
  have heq2 : (E k V'' pV'' G').Isomorphic
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c) := s1.isomorphic hC
  have hdesc : (E k V pV (C.sel k V pV)).Isomorphic
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) :=
    IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic s2' hCc (heq.symm.trans heq2)
  exact hB'.of_isomorphic hdesc.symm

theorem isCompatibleWithOpenImmersions_toAffineResolutionRule (E : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithOpenImmersions (E.toAffineResolutionRule C.sel) := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ φ _ hφ
  have : AlgebraicGeometry.SmoothOfRelativeDimension 0 φ := inferInstance
  exact isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y V pY pV
    φ 0 hφ

theorem isCompatibleWithEtaleCovers_toAffineResolutionRule (E : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithEtaleCovers (E.toAffineResolutionRule C.sel) := by
  intro k _ _ Y W pY pW _ _ _ _ _ _ _ _ φ _ hφ hsurj
  have : AlgebraicGeometry.SmoothOfRelativeDimension 0 φ := inferInstance
  have : AlgebraicGeometry.Surjective φ := ⟨hsurj⟩
  have hpb : IsPullbackBlowupSequence φ (E k W pW (C.sel k W pW)) (E k Y pY (C.sel k Y pY)) :=
    isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y W pY pW
      φ 0 hφ
  exact hpb.isStrictPullback_of_surjective
    (fun i hi => hprop k Y pY (C.sel k Y pY) i hi)

end FunctorialResolution.EmbeddedResolution

end
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRuleCompatibility

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth.{u}) :
    SmoothPullbackHasLocalAmbientEmbedding.{u} :=
  smoothPullbackHasLocalAmbientEmbedding_of_hasGraphChart hsm smoothPullbackHasGraphChart

theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding
    (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) :
    IsCompatibleWithOpenImmersions (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithOpenImmersions_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) hS hsm nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithOpenImmersions ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding
    (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) :
    IsCompatibleWithEtaleCovers (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithEtaleCovers_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw) hS hsm nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithEtaleCovers ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithOpenImmersions (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) :=
  isCompatibleWithOpenImmersions_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding A hAlg hw hemb hsncE
    hsm hex hcmp (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm)

theorem isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithEtaleCovers (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) :=
  isCompatibleWithEtaleCovers_affineResolutionRuleOfPrincipalization_of_smoothPullbackHasLocalAmbientEmbedding A hAlg hw hemb hsncE
    hsm hex hcmp (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm)

theorem isCompatibleWithFieldBaseChange_affineResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    IsCompatibleWithFieldBaseChange (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex) := by
  have key := isCompatibleWithFieldBaseChange_toAffineResolutionRule (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithFieldBaseChange A hAlg hw) nilIsStrictNormalCrossingsOfSmooth
  change IsCompatibleWithFieldBaseChange ((embeddedResolutionRuleOfPrincipalization A hw).toAffineResolutionRule
    (affineSpaceEmbeddingChoice hemb hsncE hsm)) at key
  rw [toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex] at key
  exact key

theorem isPullbackBlowupSequence_affineResolutionRuleOfPrincipalization_of_smooth (A : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hex : EmbeddedPrincipalizationYieldsBlowups A hemb hsncE hsm)
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u})
    (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k V pV)
      (affineResolutionRuleOfPrincipalization A hemb hsncE hsm hex k Y pY) := by
  have key := isPullbackBlowupSequence_presentedSelection_of_smooth (embeddedResolutionRuleOfPrincipalization A hw)
    ({ sel := affineSpaceEmbeddingChoice hemb hsncE hsm
       pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
       basePres := fun k _ _ Y p _ _ _ _ K _ _ _ hker hsncK =>
         by
           let n := ULift.{u, 0} (Fin (hemb k Y p).choose)
           have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
               (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
               (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
           have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
               (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
             AlgebraicGeometry.AffineSpace.isPullback_map (n := n) _
           exact presentationOfAmbientIso hsm _ (hemb k Y p).choose
             (hA.isoIsPullback _ _ hB) (hA.isoIsPullback_hom_snd _ _ hB) } : PresentedSelection)
    (isIndependentOfPresentedEmbedding_embeddedResolutionRule A hAlg hw hsm hcmp)
    (embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps A hAlg hw)
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization A hw)
    (smoothPullbackHasLocalAmbientEmbedding_of_affineSpaceIsSmooth hsm) hsm nilIsStrictNormalCrossingsOfSmooth
    k Y V pY pV u r hu
  rw [← toAffineResolutionRule_embeddedResolutionRuleOfPrincipalization A hw hemb hsncE hsm hex,
    EmbeddedResolutionRule.toAffineResolutionRule_apply, EmbeddedResolutionRule.toAffineResolutionRule_apply]
  exact key

end FunctorialResolution.EmbeddedResolution
end
end
