module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometryStatement

section

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.cuspidal_L2_norm_one_isometry : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a))) [ν.IsHaarMeasure], ∃ (Φ : L2cusp μ →L[ℂ] GroundTheory.Automorphic.CuspidalSpectrum.cuspidalL2 ν) (c : ℝ), 0 < c ∧ (∀ F, ‖Φ F‖ = c * ‖F‖) ∧ ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) ℂ, Φ ∘L repOp (Rcusp μ) μ f = (GroundTheory.Automorphic.CuspidalSpectrum.cuspRep ν).integrated ν (GroundTheory.Automorphic.UnitaryRep.ccToL1 ν f₁) ∘L Φ := by
  first | exact @GlobalTheory.CompanionTheory.CuspTransfer.transfer | exact GlobalTheory.CompanionTheory.CuspTransfer.transfer | (intros; apply GlobalTheory.CompanionTheory.CuspTransfer.transfer <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorOfScaledIsometricIntertwiner

section

@[expose] public section

open Topology

namespace GlobalTheory.CompanionTheory.CompactOperators

theorem isCompactOperator_of_scaled_isometric_intertwiner
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) (Φ : H →L[ℂ] K) (c : ℝ) (hc : 0 < c)
    (hΦ : ∀ x, ‖Φ x‖ = c * ‖x‖) (hAB : Φ ∘L A = B ∘L Φ) (hB : IsCompactOperator B) :
    IsCompactOperator A := by
  have hcn : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) Φ := by
    refine Φ.antilipschitz_of_bound fun x => ?_
    rw [Real.coe_toNNReal _ hcn, hΦ, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hemb : IsClosedEmbedding Φ := hanti.isClosedEmbedding Φ.uniformContinuous
  obtain ⟨S, hS, hSn⟩ := hB
  refine ⟨Φ ⁻¹' S, hemb.isCompact_preimage hS, ?_⟩
  have hpre : A ⁻¹' (Φ ⁻¹' S) = Φ ⁻¹' (B ⁻¹' S) := by
    ext x
    show Φ (A x) ∈ S ↔ B (Φ x) ∈ S
    rw [show Φ (A x) = B (Φ x) from ContinuousLinearMap.ext_iff.mp hAB x]
  rw [hpre]
  exact Φ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hSn)

end GlobalTheory.CompanionTheory.CompactOperators
end
end

-- Source module: Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot

section

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IdeleCovolume
open scoped InnerProductSpace

namespace GlobalTheory.CuspRep.CuspidalL2GL.SpecModel

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem finiteDimensional_zero (μ : Measure (GA E 0)) [μ.IsHaarMeasure] :
    FiniteDimensional ℂ (L2 (latticeGL E 0) μ) := by
  have : Subsingleton (Quot (latticeGL E 0)) := ⟨fun p q => Quotient.inductionOn₂ p q fun x y => by
    rw [Subsingleton.elim x y]⟩
  refine FiniteDimensional.of_injective (V₂ := ℂ) (K := ℂ)
    { toFun := fun F : L2 (latticeGL E 0) μ => lift (latticeGL E 0) F 1
      map_add' := fun F F' => ?_
      map_smul' := fun c F => ?_ } fun F F' e => l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (.of_forall fun x => by rw [Subsingleton.elim x 1]; exact e)
  · obtain ⟨x, hx⟩ := (ae_quotMeasure_iff.1 (Lp.coeFn_add F F')).exists
    rw [Subsingleton.elim x 1] at hx
    exact hx
  · obtain ⟨x, hx⟩ := (ae_quotMeasure_iff.1 (Lp.coeFn_smul c F)).exists
    rw [Subsingleton.elim x 1] at hx
    exact hx

end GlobalTheory.CuspRep.CuspidalL2GL.SpecModel

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactOperatorRepOpRcuspZero

section

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspRank

theorem isCompactOperator_repOp_Rcusp_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (μ : Measure (GA E 0)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E 0 → ℂ) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  have := SpecModel.finiteDimensional_zero μ
  have : FiniteDimensional ℂ (L2cusp μ) := inferInstance
  have : ProperSpace (L2cusp μ) := FiniteDimensional.proper ℂ _
  exact isCompactOperator_of_locallyCompactSpace_rng _

end GlobalTheory.CompanionTheory.CuspRank
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompact

section

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.CuspidalCompact

theorem isCompactOperator_repOp_Rcusp (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    IsCompactOperator (repOp (Rcusp μ) μ f) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact GlobalTheory.CompanionTheory.CuspRank.isCompactOperator_repOp_Rcusp_zero E μ f
  · let ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL (K := E) (n := a)) := Measure.haar
    have : ν.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
    have htransfer := GlobalTheory.T.cuspidal_L2_norm_one_isometry E a ha μ ν
    obtain ⟨Φ, c, hc0, hΦ, hint⟩ := htransfer
    obtain ⟨f₁, hf₁⟩ := hint f hf hc
    exact GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner (repOp (Rcusp μ) μ f) _ Φ c hc0 hΦ hf₁
      (GroundTheory.Automorphic.CuspidalSpectrum.isCompactOperator_cuspRep (K := E) (n := a) ν f₁)

end GlobalTheory.CompanionTheory.CuspidalCompact
end
end
