module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderMonotone
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsHypersurfaceRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.IsoBlowupRemoval
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardUniqueness
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupMarked
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsFunctoriality
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealAfterBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusDisjointBoundary
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.TwistedDivisorRestriction
import Mathlib.Tactic.Linter.Style
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryComponentsInOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantOnOpens

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.AmbientBlowupFlatBaseChange

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    {X Y S S' : Scheme.{u}} (ι : S ⟶ X) (ι' : S' ⟶ Y) (h : Y ⟶ X) (h' : S' ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι']
    [AlgebraicGeometry.Flat h]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (hsq : IsPullback ι' h' h ι)
    (s : BlowupSequenceData S) (s' : BlowupSequenceData S')
    (hs : s.CentersContainNoComponent) (hs' : s'.CentersContainNoComponent)
    (hpb : IsStrictPullbackBlowupSeq h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq h (ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  have hstrict : IsStrictPullbackBlowupSeq h
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) h
  have hN : ∀ i : ℕ, i ≤ ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).length →
      AlgebraicGeometry.IsLocallyNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  have hN' : ∀ i : ℕ, i ≤ (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).length →
      AlgebraicGeometry.IsLocallyNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) :=
      isNoetherian_schemeAt
        (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) i hi
    infer_instance
  have hpushTb : IsPushforwardBlowupSeq ι' s'.toSequenceOfBlowups
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) :=
    IsPushforwardBlowupSeq.of_flat_isPullback ι ι' h h' hsq s.toSequenceOfBlowups
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) s'.toSequenceOfBlowups
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN hN'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hpb hstrict
  have hequiv : ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).Isomorphic
      ((ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups) :=
    IsPushforwardBlowupSeq.isomorphic ι' hpushTb
      (isPushforwardBlowupSeq_ambientBlowupSequence ι' s' hres hno hs')
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback hstrict hequiv

theorem isPullbackBlowupSequence_ambientBlowupSequence_of_flat
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    {X Y S S' : Scheme.{u}} (ι : S ⟶ X) (ι' : S' ⟶ Y) (h : Y ⟶ X) (h' : S' ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι']
    [AlgebraicGeometry.Flat h]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (hsq : IsPullback ι' h' h ι)
    (s : BlowupSequenceData S) (s' : BlowupSequenceData S')
    (hs : s.CentersContainNoComponent) (hs' : s'.CentersContainNoComponent)
    (hpb : IsPullbackBlowupSequence h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsPullbackBlowupSequence h (ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  have : AlgebraicGeometry.Flat h' := by
    rw [← hsq.isoPullback_hom_snd]
    infer_instance
  have hUstrict : IsStrictPullbackBlowupSeq h' (s.toSequenceOfBlowups.baseChange h') s.toSequenceOfBlowups :=
    isStrictPullbackSequenceOfBlowups_baseChange s.toSequenceOfBlowups h'
  have hstrict : IsStrictPullbackBlowupSeq h
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) h
  have hN : ∀ i : ℕ, i ≤ ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).length →
      AlgebraicGeometry.IsLocallyNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  have hN' : ∀ i : ℕ, i ≤ (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).length →
      AlgebraicGeometry.IsLocallyNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) :=
      isNoetherian_schemeAt
        (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) i hi
    infer_instance
  have hpushTb : IsPushforwardBlowupSeq ι' (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) :=
    IsPushforwardBlowupSeq.of_flat_isPullback ι ι' h h' hsq s.toSequenceOfBlowups
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN hN'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hUstrict hstrict
  have hpushPrune : IsPushforwardBlowupSeq ι' (s.toSequenceOfBlowups.baseChange h').withoutIsoBlowups
      ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups :=
    isPushforwardSequenceOfBlowups_withoutIsoBlowups ι' (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN' hpushTb
  have heq : ((s.toSequenceOfBlowups.baseChange h').withoutIsoBlowups).Isomorphic s'.toSequenceOfBlowups :=
    IsPullbackBlowupSequence.isomorphic hUstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hpb
  have hpush' : IsPushforwardBlowupSeq ι' s'.toSequenceOfBlowups
      ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups :=
    IsPushforwardBlowupSeq.of_isomorphic_source ι' heq hpushPrune
  have hequivT : (((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups).Isomorphic
      ((ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups) :=
    IsPushforwardBlowupSeq.isomorphic ι' hpush'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι' s' hres hno hs')
  exact IsPullbackBlowupSequence.of_isomorphic hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hequivT

end FunctorialResolution.EmbeddedResolution
end
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdealTop

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (hm : T.mult = 1)
    (hlow : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hpush : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    DivisorReduction.containedComponentsIdeal T j hj = ⊤ := by
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hnz : NonzeroOnComponents J := hlow.nonzeroOnComponents
    have hcomap : T.ideal.comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
      rw [hpush]
      exact Blowup.comap_map_of_isClosedImmersion _ J
    have hsub : ∀ y : ↥(T.boundary.get ⟨j, hj⟩).subscheme,
        (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ (T.ideal.support : Set ↥T.scheme) →
        y ∈ (J.support : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := by
      intro y hy
      have h1 := (one_le_orderAt_iff_mem_support T.ideal
        ((T.boundary.get ⟨j, hj⟩).subschemeι y)).mpr hy
      have h2 := orderAt_le_orderAt_comap (T.boundary.get ⟨j, hj⟩).subschemeι T.ideal y
      rw [hcomap] at h2
      exact (one_le_orderAt_iff_mem_support J y).mp (le_trans h1 h2)
    have hempty : divisorComponentsInOrderLocus T j hj = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => ((Set.mem_empty_iff_false x).mp hx).elim⟩
      exfalso
      obtain ⟨C, hCpre, hxC, hCmax⟩ :=
        exists_preirreducible ({x} : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)
          isIrreducible_singleton.2
      have hxC' : x ∈ C := hxC rfl
      have hC : C ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
        ⟨⟨⟨x, hxC'⟩, hCpre⟩, fun u hu hCu => le_of_eq (hCmax u hu.2 hCu)⟩
      refine hnz C hC ?_
      intro y hyC
      have hyc : y ∈ connectedComponent x :=
        hCpre.isPreconnected.subset_connectedComponent hxC' hyC
      have h1 := hx hyc
      rw [hm] at h1
      have h1' : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ orderAtLeastLocus T.ideal 1 := h1
      exact hsub y ((mem_orderAtLeastLocus_one_iff T.ideal _).mp h1')
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty,
      support_openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩
        (isClosed_divisorComponentsInOrderLocus T hV j hj), Set.image_eq_empty]
    exact hempty
  · exact EmbeddedResolution.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BalancedDivisorReduction

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem lowerIdealWithoutBlowup_eq_ideal (T : MarkedIdealWithBoundary.{u}) :
    DivisorReduction.lowerIdealWithoutBlowup T = T.ideal := by
  show T.ideal.comap (CategoryTheory.CategoryStruct.id T.scheme) = T.ideal
  exact Scheme.IdealSheafData.comap_id _

private theorem orderAt_le_mult_of_isOrderBoundedByMult (T : MarkedIdealWithBoundary.{u}) (hOB : T.IsOrderBoundedByMult) :
    ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) := hOB

private theorem isDerivBalanced_of_isBalanced (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) :
    ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult := by
  intro _
  exact hbal

private theorem goingUpInvariant_length_of_isBalanced (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hbal : T.IsBalanced hV.locallyOfFiniteType)
    [AlgebraicGeometry.IsNoetherian T.scheme]
    [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (hVlow : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent) :
    DivisorReduction.GoingUpInvariant hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
      (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr s.length := by
  have hbalLower : IsDerivBalanced T.base T.structMap (DivisorReduction.lowerIdealWithoutBlowup T) T.mult := by
    rw [lowerIdealWithoutBlowup_eq_ideal]
    exact hbal
  have hE₀ : InStrictNormalCrossingPosition T.structMap (DivisorReduction.lowerBoundaryWithoutBlowup T) := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    exact hV.snc
  have hjE : j < (DivisorReduction.lowerBoundaryWithoutBlowup T).length := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    exact hj
  have hget : (DivisorReduction.lowerBoundaryWithoutBlowup T)[j]'hjE = T.boundary[j]'hj := by
    simp [DivisorReduction.lowerBoundaryWithoutBlowup_eq T]
  have hlen : ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j).length = T.boundary.length - 1 := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [← hlen, List.take_length]
  exact DivisorReduction.goingUpInvariant_of_le hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr hbalLower hV.one_le_mult hVlow hlift hE₀ hjE hget
    htrunc s.length le_rfl

theorem divisorReductionProperties_of_blowupPreservesNoetherian (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : DivisorReductionProperties hres hno := by
  have hlift : StrictNormalCrossingsLiftFromDivisor.{u} := hasStrictNormalCrossingsWith_ker_cons_of_comap
  exact
    { isMarked_pushedTop := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr
        have := inst
        exact DivisorReduction.isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow s hpr
      isMarked_pushedPre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr
        have := inst
        exact DivisorReduction.isMarked_prepend_ambientBlowupSeq hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
          s hpr
          (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
          (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
          (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
          (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
          (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
            (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
      valid_lowerPre := by
        intro T hV hOB hbal j hj hZ
        exact DivisorReduction.isAdmissible_restrictTwistedToDivisor T hV hOB hbal j hj hZ
      orderAt_ctrlIdeal_le_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr i hi x
        have := inst
        have := hV.charZero
        have := hV.smooth
        exact orderAt_controlledTransform_le_of_isMarked T.base T.structMap T.ideal T.mult T.boundary
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr)
          (DivisorReduction.isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow
            s hpr)
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) i
          (by rw [DivisorReduction.ambientBlowupSeq_length]; exact hi) x
      orderAt_ctrlIdeal_le_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr i hi x
        have := inst
        have := hV.charZero
        have := hV.smooth
        exact orderAt_controlledTransform_le_of_isMarked T.base T.structMap T.ideal T.mult T.boundary
          (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr))
          (DivisorReduction.isMarked_prepend_ambientBlowupSeq hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
            s hpr
            (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
            (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
            (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
            (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
            (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
              (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)))
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) i
          (by rw [BlowupSequenceData.prepend_length, DivisorReduction.ambientBlowupSeq_length]; exact hi) x
      coSupport_inter_ker_eq_empty_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr hempty
        have := inst
        have := hV.charZero
        have := hV.smooth
        have := hV.locallyOfFiniteType
        have hgoingUp := goingUpInvariant_length_of_isBalanced hres hno hlift T hV hbal j hj hVlow s hpr
        exact DivisorReduction.orderAtLeastLocus_inter_support_ker_eq_empty hres hno T j hj s hpr
          (fun i hi => hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i hi) hempty
      coSupport_inter_ker_eq_empty_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr hempty
        have := inst
        have := hV.charZero
        have := hV.smooth
        have := hV.locallyOfFiniteType
        obtain ⟨U₀, hU, hsupp, hbalPre, hinv⟩ :=
          DivisorReduction.exists_isClosed_opens_goingUpInvariantOnOpen hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
            s hpr
            (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
            (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
            (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
            (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
            (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
              (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
        exact DivisorReduction.orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty hres hno T j hj hb s hpr
          (fun i hi => (hinv s.length le_rfl).exists_pow_mul_eq_comap_controlledTransform i hi)
          (DivisorReduction.controlledTransform_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr) hempty
      isPullbackSeq_ambientTower := by
        intro X Y S S' σ σ' φ ψ _ _ _ _ _ hsq d d' hc hc' hpb
        exact isPullbackBlowupSequence_ambientBlowupSequence_of_flat hres hno σ σ' φ ψ hsq d d' hc hc' hpb
      isStrictPullbackSeq_ambientTower := by
        intro X Y S S' σ σ' φ ψ _ _ _ _ _ hsq d d' hc hc' hpb
        exact isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat hres hno σ σ' φ ψ hsq d d' hc hc' hpb
      comap_ctrlIdeal_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr i hi
        have := inst
        exact DivisorReduction.comap_controlledTransform_of_containedComponentsIdeal_eq_top hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow
          s hpr i hi
      comap_ctrlIdeal_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr i hi
        have := inst
        exact DivisorReduction.comap_controlledTransform_prepend_ambientBlowupSeq hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
          s hpr
          (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
          (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
          (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
          (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
          (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
            (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
          i hi
      preIdeal_baseChange := by
        intro T hV L _ _ f hV' j hj hj'
        exact containedComponentsIdeal_baseChange T hV L f hV' j hj hj'
      preIdeal_pullbackAlong := by
        intro T hV Y q h _ hq hV' j hj hj'
        exact containedComponentsIdeal_pullbackAlong_of_smooth T hV Y q h hq hV' j hj hj'
      preIdeal_eq_top_of_imageIdeal := by
        intro T hV j hj J hm hlow hpush
        exact DivisorReduction.containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf T hV j hj J hm hlow hpush }

end FunctorialResolution.EmbeddedResolution

end
end
end
