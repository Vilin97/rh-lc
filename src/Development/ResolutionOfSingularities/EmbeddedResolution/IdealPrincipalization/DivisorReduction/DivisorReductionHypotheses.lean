module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyPulledBackCenter
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Prepend
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionPushforward
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerDimensionSmoothPullback

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryPositionInvariance

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁))
    (hV₁ : (T.withBoundary L₁).IsAdmissible) (hV₂ : (T.withBoundary L₂).IsAdmissible) :
    IsStrictPullbackBlowupSeq (𝟙 T.scheme)
      (((canonicalAlgorithmRules hres).divisorFamily L j₂ (T.withBoundary L₂)).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j₁ (T.withBoundary L₁)).toSequenceOfBlowups) := by
  classical
  by_cases hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · have hN : AlgebraicGeometry.IsNoetherian T.scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
    have hN₁ : AlgebraicGeometry.IsNoetherian (T.withBoundary L₁).scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV₁
    have hN₂ : AlgebraicGeometry.IsNoetherian (T.withBoundary L₂).scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV₂
    have hflat : AlgebraicGeometry.Flat (𝟙 T.scheme) := inferInstance
    have hjb₁ : j₁ < (T.withBoundary L₁).boundary.length := hj₁
    have hjb₂ : j₂ < (T.withBoundary L₂).boundary.length := hj₂
    have hpre : DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁ =
        DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂ :=
      DivisorReduction.containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq
    have hs₁ : _ ∨ _ := hshape j₁ (T.withBoundary L₁) hV₁ hjb₁ hdim hO hbal hcs
    have hs₂ : _ ∨ _ := hshape j₂ (T.withBoundary L₂) hV₂ hjb₂ hdim hO hbal hcs
    simp only [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
    rcases hs₁ with ⟨hZ₁, hpr₁, hmk₁, he₁⟩ | ⟨hZ₁, hb₁, hpr₁, hmk₁, he₁⟩
    · rcases hs₂ with ⟨hZ₂, hpr₂, hmk₂, he₂⟩ | ⟨hZ₂, hb₂, hpr₂, hmk₂, he₂⟩
      · have hstep : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₂))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₂))
              (L (DivisorReduction.restrictToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₁))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₁))
              (L (DivisorReduction.restrictToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
            ((L₁.get ⟨j₁, hj₁⟩).subscheme) ((L₂.get ⟨j₂, hj₂⟩).subscheme)
            ((L₁.get ⟨j₁, hj₁⟩).subschemeι) ((L₂.get ⟨j₂, hj₂⟩).subschemeι)
            (𝟙 T.scheme) _
            ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₁))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₁)) T.scheme (𝟙 T.scheme)
              (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq)).flip)
            _ _ hpr₁ hpr₂
            (IsStrictPullbackBlowupSeq.ofMarkedSequence
              (A := DivisorReduction.restrictToDivisor (T.withBoundary L₂) j₂ hjb₂)
              (B := DivisorReduction.restrictToDivisor (T.withBoundary L₁) j₁ hjb₁) _ _ _
              (DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_get_eq_of_eq_top hres hfacts n L O hL hbc hsh
                T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hdim hO hbal hcs hV₂ hdim hO hbal hcs hZ₁))
        rw [he₁, he₂]
        simp only [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hstep
      · exact absurd (hpre.symm.trans hZ₁) hZ₂
    · rcases hs₂ with ⟨hZ₂, hpr₂, hmk₂, he₂⟩ | ⟨hZ₂, hb₂, hpr₂, hmk₂, he₂⟩
      · exact absurd (hpre.trans hZ₂) hZ₁
      · have hcomap : (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
            (𝟙 (T.withBoundary L₁).scheme) =
            DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁ := by
          rw [Scheme.IdealSheafData.comap_id]
        have hZZ : DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂ =
            (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
              (𝟙 (T.withBoundary L₁).scheme) := hpre.symm.trans hcomap.symm
        have hb₁' : Blowup.IsBlowupAlongIdealSheaf (𝟙 (T.withBoundary L₁).scheme)
            ((DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
              (𝟙 (T.withBoundary L₁).scheme)) := by
          rw [hcomap]
          exact hb₁
        have hstep : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
            ((L₁.get ⟨j₁, hj₁⟩).subscheme) ((L₂.get ⟨j₂, hj₂⟩).subscheme)
            ((L₁.get ⟨j₁, hj₁⟩).subschemeι) ((L₂.get ⟨j₂, hj₂⟩).subschemeι)
            (𝟙 T.scheme) _
            ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁) T.scheme (𝟙 T.scheme)
              (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq)).flip)
            _ _ hpr₁ hpr₂
            (IsStrictPullbackBlowupSeq.ofMarkedSequence
              (A := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)
              (B := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁) _ _ _
              (DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor_of_get_eq hres hfacts n L O hL hbc hsh
                T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hdim hO hbal hcs hV₂ hdim hO hbal hcs hZ₁))
        have hfin : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂) hb₂
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂
                hjb₂ (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
                (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
                (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂)).toSequenceOfBlowups
            (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁) hb₁
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁
                hjb₁ (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
                (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
                (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁)).toSequenceOfBlowups := by
          rw [BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZZ hb₂ hb₁'
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂)]
          exact IsStrictPullbackBlowupSeq.prepend hstep _ hb₁ hb₁'
        rw [he₁, he₂]
        simp only [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hfin
  · have hcs0 : orderAtLeastLocus T.ideal T.mult = ∅ := Set.not_nonempty_iff_eq_empty.mp hcs
    exact IsStrictPullbackBlowupSeq.of_length_zero _ _ _
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j₂ (T.withBoundary L₂) hV₂ hdim hO hbal
        hj₂ hcs0)
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j₁ (T.withBoundary L₁) hV₁ hdim hO hbal
        hj₁ hcs0)

theorem strictBoundaryReindexingInvariance_of_divisorReductionSeqEqAmbient
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj) :
    DivisorReduction.StrictBoundaryReindexingInvariance hres n L :=
  ⟨fun T hV hdim hO hbal L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hV₂ =>
    isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq hres hfacts hbc hsh n L O hL hshape T hV hdim hO hbal
      L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hV₂⟩

theorem isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj) :
    IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  DivisorReduction.isBoundaryPositionInvariant_divisorFamily hres n L
    (strictBoundaryReindexingInvariance_of_divisorReductionSeqEqAmbient hres hfacts hbc hsh n L O hL hshape)

end FunctorialResolution.EmbeddedResolution

end
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

structure DivisorReductionHypotheses (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) : Prop where
  trivial_of_coSupport_empty :
    ∀ (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      j < T.boundary.length →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h],
        h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
          (orderAtLeastLocus T.ideal T.mult).Nonempty →
          orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
          ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
            IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)
  baseChange : SmoothPullbackCompatibility.{u}
  smoothImpliesFlat : FlatOfSmooth.{u}
  degenerateTransversal : EmptyPulledBackCenterCompatibility.{u}
  fieldBaseChangeCompatibility : FieldBaseChangeCompatibility.{u}
  boundaryReindexingInvariance : BoundaryReindexingInvariance.{u}
  fieldLower : DivisorRestrictionFieldBaseChange.{u}
  divisorReduction : DivisorReductionStepProperties hres blowupPreservesNoetherian
  pushedBlowupSequenceProperties : PushedBlowupSequenceProperties hres blowupPreservesNoetherian

theorem DivisorReductionHypotheses.divisorReductionTerminationProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) :
    DivisorReductionTerminationProperties hres blowupPreservesNoetherian :=
  hin.divisorReduction.toDivisorReductionTerminationProperties

theorem DivisorReductionHypotheses.trivialPullbackBlowupSequence {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) (L : PrincipalizationAssignment.{u}) (j : ℕ) :
    IsPullbackSeqOfEmptyBlowupSeq hres L j :=
  pullbackOfEmptySequence_of_isPullbackSequenceOfBlowups hres L j
    (fun T hV hj Y q h _ hq E' hV' hcs hcs' B' hB' =>
      hin.trivial_of_coSupport_empty L j T hV hj Y q h hq E' hV' hcs hcs' B' hB')

theorem DivisorReductionHypotheses.divisorReductionSeqEqAmbient {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (_hL : IsMaxOrderReduction (fun d => d < n) L O) :
    ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj := by
  intro j T hV hj _hdim hO hD hcs
  have : AlgebraicGeometry.IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have h := divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hin.divisorReductionTerminationProperties L j T hV hj hO hD hcs.ne_empty
  rcases h with ⟨hZ, hpr, hmk, hstep⟩ | ⟨hZ, hb, hpr, hmk, hstep⟩
  · exact Or.inl ⟨hZ, hpr, hmk, hstep hmk⟩
  · exact Or.inr ⟨hZ, hb, hpr, hmk, hstep hmk⟩

end DivisorReduction

private theorem strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    DivisorReduction.StrictPullbackOfSmoothBaseChangeOnDivisor n L j := by
  constructor
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'

theorem isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      ∀ (j : ℕ),
        IsBoundaryDivisorReduction (fun d => d ≤ n) j ((canonicalAlgorithmRules hres).divisorFamily L j) L := by
  intro n L O hL j
  have hshapeN : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs => hin.divisorReductionSeqEqAmbient n L O hL j T hV hj hdim hO hbal hcs
  have hshapeE : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs =>
      hshapeN T hV hj hdim hO hbal (Set.nonempty_iff_ne_empty.mpr hcs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E' hBE htake
      hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties
      hin.baseChange hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E'
      hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj i hi x
    exact divisorFamily_canonicalAlgorithmRules_orderAt_le_mult hres hin.divisorReductionTerminationProperties n L j T hV hdim hO hbal hj i hi x
  · intro T hV hdim hO hbal hj i hi
    exact divisorFamily_canonicalAlgorithmRules_center_nonempty hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO hbal
      hj i hi
  · intro T hV hdim hO hbal hj hm J hVJ hdimJ him
    exact isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO
      (fun _ => hbal) hj hm J hVJ hdimJ him
  · intro T hV hdim hO hbal hj
    obtain ⟨D, b, h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties hin.pushedBlowupSequenceProperties n L O hL j T hV hdim hO
        hbal hj
    refine ⟨D, b, h1, h2, h3, h4, ?_, h6, ?_⟩
    · intro t ht hb
      exact h5 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
    · intro t ht hb
      exact h7 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
  · intro T hV hdim hO hbal hj Y q h _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j (hin.trivialPullbackBlowupSequence L j)
      (restrictedSmoothPullback_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
        hin.degenerateTransversal n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_of_smooth hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j
      (strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj hcs
    exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs

theorem isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  fun n L O hL =>
    isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient hres hin.divisorReductionTerminationProperties hin.baseChange hin.boundaryReindexingInvariance
      n L O hL (hin.divisorReductionSeqEqAmbient n L O hL)

end FunctorialResolution.EmbeddedResolution

end
end
end
