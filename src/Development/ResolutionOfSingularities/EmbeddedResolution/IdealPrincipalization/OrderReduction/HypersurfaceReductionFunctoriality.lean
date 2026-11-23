module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.SameNontrivialBoundary
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.ContinuationComparison
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TrivialDivisorContinuation
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
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.FaithfullyFlatDescent
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.LowerDimensionalContinuation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparationPullbackComparison

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace NontrivialBoundary

theorem nonempty_separateBoundaryPullbackComparison
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    Nonempty (SequenceOfBlowupsPullback q
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  classical
  have : AlgebraicGeometry.Flat q := inferInstance
  revert hj
  induction j with
  | zero =>
    intro _
    have e0 : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S 0
        = FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary :=
      MaxContactCoverData.separateBoundary_zero hinv T (fun S₀ _ i => A i S₀) S
    have e0' : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q 0)
        = FunctorialResolution.EmbeddedResolution.emptyMarkedBlowupSequenceData (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary := by
      rw [NontrivialBoundary.survivingBoundaryCount_zero]
      exact MaxContactCoverData.separateBoundary_zero hinv T (fun S₀ _ i => A i S₀)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
    rw [e0, e0']
    simp only [FunctorialResolution.EmbeddedResolution.MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups]
    refine ⟨SequenceOfBlowupsPullback.ofCentersMissImage q _ ?_ _ ?_⟩
    · intro i hi
      simp at hi
    · simp
  | succ j ih =>
    intro hj1
    have hjS : j < S.boundary.length := Nat.lt_of_succ_le hj1
    obtain ⟨D⟩ := ih (Nat.le_of_succ_le hj1)
    have hftS : AlgebraicGeometry.LocallyOfFiniteType
        ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).proj
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length ≫ S.structMap) :=
      BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV _ _ le_rfl
    have hftT : AlgebraicGeometry.LocallyOfFiniteType
        ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.survivingBoundaryCount S q j)).proj
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.survivingBoundaryCount S q j)).length
          ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap) :=
      BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
        _ _ le_rfl
    have hm : 1 ≤ S.mult := hV.one_le_mult
    have hdimU : (MaxContactCoverData.derivedTriple S
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0).krullDimSucc ≤ T.krullDimSucc :=
      hstar.derivedTriple_dim_le (T := T) hV (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0 hdimS
    have hPU :
        P (MaxContactCoverData.derivedTriple S (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS [] 0).krullDimSucc :=
      hmono _ _ hdimU hPdimT
    have hVU := BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar S hV
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) hftS
    have hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) hftT [] 0).krullDimSucc ≤ T.krullDimSucc :=
      hstar.derivedTriple_dim_le (T := T) hV'
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        hftT [] 0 hdim'
    have hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) hftT [] 0).krullDimSucc :=
      hmono _ _ hdimU' hPdimT
    have hVU' := BoundarySeparationBaseChange.isAdmissible_derivedTriple_nil hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j))
      hftT
    have hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
        orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞) :=
      fun x => BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO x
    have eS : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S (j + 1)
        = MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) S
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j) [] 0 j :=
      MaxContactCoverData.separateBoundary_succ hinv T (fun S₀ _ i => A i S₀) S j
    by_cases hlive : (S.boundary[j]'hjS).comap q = ⊤
    · have eT : NontrivialBoundary.survivingBoundaryCount S q (j + 1) = NontrivialBoundary.survivingBoundaryCount S q j :=
        NontrivialBoundary.survivingBoundaryCount_succ_of_eq_top S q j hjS hlive
      rw [eS, eT]
      have hjlen : j < ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).boundary
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length).length :=
        lt_of_lt_of_le hjS
          (NontrivialBoundary.length_boundary_le_length_lastBoundary S (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j))
      have hBoundaryTop : (((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).boundary
              (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).length).get ⟨j, hjlen⟩).comap D.lastMap
          = ⊤ := by
        rw [List.get_eq_getElem]
        exact NontrivialBoundary.lastBoundary_comap_lastMap_eq_top S q
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
          (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q j)) D hstar hV hV' j hjS hlive
      exact TrivialDivisorContinuation.nonempty_pullback_appendLowerDimReduction_of_comap_eq_top P A Bl j S q
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        D hftS hstar (hspec j) hV hm hO hPU hVU hjlen hBoundaryTop hinv T hdimU
    · have eT : BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.survivingBoundaryCount S q (j + 1))
          = MaxContactReduction.appendLowerDimReduction hinv T (fun S₀ _ i => A i S₀) (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
                (NontrivialBoundary.survivingBoundaryCount S q j)) [] 0 (NontrivialBoundary.survivingBoundaryCount S q j) := by
        rw [NontrivialBoundary.survivingBoundaryCount_succ_of_ne_top S q j hjS hlive]
        exact MaxContactCoverData.separateBoundary_succ hinv T (fun S₀ _ i => A i S₀)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (NontrivialBoundary.survivingBoundaryCount S q j)
      rw [eS, eT]
      exact ⟨BoundaryDeletion.continuationComparison (P := P) (A := A) (Bl := Bl) (j := j) (S := S)
        (q := q) (s := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j)
        (s' := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.survivingBoundaryCount S q j))
        (Dt := D) (hftS := hftS) (hftT := hftT) (hinv := hinv) (T := T)
        (hstar := hstar) (hspec := hspec j) (hspec' := hspec (NontrivialBoundary.survivingBoundaryCount S q j))
        (hshift := hshift) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
        (hj := hjS) (hlive := hlive) (hPU := hPU) (hVU := hVU) (hPU' := hPU') (hVU' := hVU')
        (hdimU := hdimU) (hdimU' := hdimU')⟩

def separateBoundaryPullbackComparison
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (hstar : MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (j : ℕ) (hj : j ≤ S.boundary.length) :
    SequenceOfBlowupsPullback q
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.survivingBoundaryCount S q j)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S j).toMarkedSequenceOfBlowups.toSequenceOfBlowups :=
  (nonempty_separateBoundaryPullbackComparison P hmono A Bl hspec hshift hstar hinv T hPdimT S q hV hO hdimS hV' hdim'
    j hj).some

end NontrivialBoundary

end FunctorialResolution.EmbeddedResolution

end
end
end

-- Source module: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.HypersurfaceReductionFunctoriality

section

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

theorem isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (T : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T.krullDimSucc)
    (hH' : ∀ [AlgebraicGeometry.LocallyOfFiniteType (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      IsMaxContactHypersurface (NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (H.comap q))
    (hH'snc : InStrictNormalCrossingPosition (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap [H.comap q]) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S₀ _ i => A i S₀)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (fun S₀ _ i => A i S₀) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hcnt : NontrivialBoundary.survivingBoundaryCount S q S.boundary.length
      = (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length := NontrivialBoundary.survivingBoundaryCount_length_eq S q
  have Dt0 := NontrivialBoundary.separateBoundaryPullbackComparison P hmono A Bl hspec hshift hstar hinv T hPdimT S q hV hO
    hdimS hV' hdim' S.boundary.length le_rfl
  rw [hcnt] at Dt0
  have hftS : AlgebraicGeometry.LocallyOfFiniteType
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length ≫ S.structMap) :=
    BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar S hV _ _ le_rfl
  have hftT : AlgebraicGeometry.LocallyOfFiniteType
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length
        ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap) :=
    BoundarySeparationByMaxContact.locallyOfFiniteType_projectionToBase_comp hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' _ _
      le_rfl
  have hF := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A Bl hspec T hPdimT S
    hV hO hdimS H hHsnc S.boundary.length le_rfl
  have hF' := BoundarySeparationBaseChange.separateBoundaryInvariant_separateBoundaryOfFamily hstar hinv P hmono A Bl hspec T hPdimT
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' (BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO) hdim' (H.comap q)
    hH'snc (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length le_rfl
  have hm : 1 ≤ S.mult := hV.one_le_mult
  have hO' : ∀ x : ↥(NontrivialBoundary.pullbackWithNontrivialBoundary S q).scheme,
      orderAt (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal x ≤ ((S.mult : ℕ) : ℕ∞) :=
    BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO
  have hdimU : (MaxContactCoverData.derivedTriple S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    hstar.derivedTriple_dim_le hV _ hftS _ _ hdimS
  have hPU : P (MaxContactCoverData.derivedTriple S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
      S.boundary.length).krullDimSucc := hmono _ _ hdimU hPdimT
  have hsncU : InStrictNormalCrossingPosition
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length ≫ S.structMap)
      ([MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H] ++
        List.drop S.boundary.length
          ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).boundary
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length).length)) := by
    simpa [MaxContactReduction.strictTransformAtLength_eq] using
      inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar S hV hO H (@hH hV.locallyOfFiniteType)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hF.2.2 _ le_rfl
  have hVU := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar S hV
    (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) hftS
    [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) H]
    S.boundary.length hsncU
  have hdimU' : (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc ≤ T.krullDimSucc :=
    hstar.derivedTriple_dim_le hV' _ hftT _ _ hdim'
  have hPU' : P (MaxContactCoverData.derivedTriple (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
      [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).krullDimSucc := hmono _ _ hdimU' hPdimT
  have hsncU' : InStrictNormalCrossingPosition
      ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).proj
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length
        ≫ (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap)
      ([MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)] ++
        List.drop (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length
          ((BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
            (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).boundary
            (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
              (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length).length)) := by
    simpa [MaxContactReduction.strictTransformAtLength_eq] using
      inStrictNormalCrossingPosition_iteratedStrictTransform_cons_drop hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
        (BoundarySeparationBaseChange.orderAt_pullbackTriple_le_mult S q hV hO) (H.comap q) (@hH' hV'.locallyOfFiniteType)
        (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
          (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hF'.2.2 _ le_rfl
  have hVU' := BoundarySeparationByMaxContact.isAdmissible_derivedTriple hstar (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV'
    (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) hftT
    [MaxContactReduction.strictTransformAtLength (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length) (H.comap q)]
    (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length hsncU'
  have hsep : BoundarySeparationByMaxContact.BoundarySeparated S
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length) S.boundary.length := hF.1
  have hsep' : BoundarySeparationByMaxContact.BoundarySeparated (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length := hF'.1
  simp only [MaxContactCoverData.reduceAlongHypersurface_eq_appendLowerDimReduction]
  exact StrictTransformComparison.isPullbackBlowupSequence_appendLowerDimReduction (P := P) (A := A) (Bl := Bl) (S := S) (q := q)
    (s := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A S S.boundary.length)
    (s' := BoundarySeparationBaseChange.separateBoundaryOfFamily hinv T A (NontrivialBoundary.pullbackWithNontrivialBoundary S q)
      (NontrivialBoundary.pullbackWithNontrivialBoundary S q).boundary.length)
    (Dt := Dt0) (hftS := hftS) (hftT := hftT) (hinv := hinv) (T := T) (hstar := hstar)
    (hspec := hspec 0) (H := H) (hV := hV) (hV' := hV') (hm := hm) (hO := hO) (hO' := hO')
    (hdimU := hdimU) (hPU := hPU) (hVU := hVU) (hdimU' := hdimU') (hPU' := hPU') (hVU' := hVU')
    (hsep := hsep) (hsep' := hsep')

theorem isPullbackBlowupSequence_reduceAlongHypersurface_lowerDimensionalFamily
    (hstar : _root_.FunctorialResolution.EmbeddedResolution.MaxContactCoverProperties.{u})
    (_hin : _root_.FunctorialResolution.EmbeddedResolution.OrderReduction.OrderReductionHypotheses)
    (_hMC : _root_.FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.IsMaxContactInvariantBalancedTuned.{u})
    (_hAdm : _root_.FunctorialResolution.EmbeddedResolution.BoundarySeparationBaseChange.MaxContactHypersurfaceSmoothPullback.{u})
    (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (Bl : PrincipalizationAssignment.{u})
    (hspec : ∀ i : ℕ, IsBoundaryDivisorReduction P i (A i) Bl)
    (hshift : IsBoundaryPositionInvariant P A)
    (T T' : MarkedIdealWithBoundary.{u}) (hPdimT : P T.krullDimSucc) (hPdimOther : P T'.krullDimSucc)
    (S : MarkedIdealWithBoundary.{u}) (hV : S.IsAdmissible)
    (hO : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ (S.mult : ℕ∞))
    (hdimS : S.krullDimSucc ≤ T.krullDimSucc)
    (_hBoundaryNeTop : ∀ D ∈ S.boundary, D ≠ ⊤)
    (H : S.scheme.IdealSheafData)
    (hH : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H)
    (hHsnc : InStrictNormalCrossingPosition S.structMap [H])
    {X' : Scheme.{u}} (q : X' ⟶ S.scheme) [AlgebraicGeometry.Smooth q]
    (hV' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).IsAdmissible)
    (hdim' : (NontrivialBoundary.pullbackWithNontrivialBoundary S q).krullDimSucc ≤ T'.krullDimSucc)
    (hH' : ∀ [AlgebraicGeometry.LocallyOfFiniteType (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap],
      IsMaxContactHypersurface (NontrivialBoundary.pullbackWithNontrivialBoundary S q).base
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap (NontrivialBoundary.pullbackWithNontrivialBoundary S q).ideal
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q).mult (H.comap q))
    (hH'snc : InStrictNormalCrossingPosition (NontrivialBoundary.pullbackWithNontrivialBoundary S q).structMap [H.comap q]) :
    IsPullbackBlowupSequence q
      (MaxContactReduction.reduceAlongHypersurface hinv T' (lowerDimensionalFamily A T')
        (NontrivialBoundary.pullbackWithNontrivialBoundary S q) (H.comap q)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      (MaxContactReduction.reduceAlongHypersurface hinv T (lowerDimensionalFamily A T) S H).toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  rcases le_total T.krullDimSucc T'.krullDimSucc with hle | hle
  · rw [reduceAlongHypersurface_congr_of_dim_le hstar hinv A T T' hle S hV hdimS H]
    exact isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth hstar hinv P hmono A Bl hspec hshift T' hPdimOther S hV hO
      (le_trans hdimS hle) H hH hHsnc q hV' hdim' hH' hH'snc
  · rw [reduceAlongHypersurface_congr_of_dim_le hstar hinv A T' T hle (NontrivialBoundary.pullbackWithNontrivialBoundary S q) hV' hdim'
      (H.comap q)]
    exact isPullbackBlowupSequence_reduceAlongHypersurface_of_smooth hstar hinv P hmono A Bl hspec hshift T hPdimT S hV hO hdimS
      H hH hHsnc q hV' (le_trans hdim' hle) hH' hH'snc

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution

end
end
end
