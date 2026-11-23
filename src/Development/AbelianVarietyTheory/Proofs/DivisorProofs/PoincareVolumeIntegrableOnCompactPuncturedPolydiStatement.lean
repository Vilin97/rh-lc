module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnInvMulLogSqNearZero

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem continuousAt_inv_log_zero : ContinuousAt (fun t : ℝ => (Real.log t)⁻¹) 0 := by
  unfold ContinuousAt
  simp only [Real.log_zero, inv_zero]
  refine Tendsto.mono_left (x := 𝓝[≠] (0:ℝ) ⊔ pure 0) ?_ (nhdsNE_sup_pure (0:ℝ)).ge
  refine Tendsto.sup ?_ ?_
  · exact tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero
  · rw [tendsto_pure_left]
    intro s hs
    simpa using mem_of_mem_nhds hs

theorem integrableOn_inv_mul_log_sq :
    IntegrableOn (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2) (Set.Ioc 0 (1 / 2)) := by
  have hcont : ContinuousOn (fun t : ℝ => -(Real.log t)⁻¹) (Set.Icc 0 (1 / 2)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      exact (continuousAt_inv_log_zero.neg).continuousWithinAt
    · have hlog : Real.log t ≠ 0 := by
        have : Real.log t < 0 := Real.log_neg h (by linarith [ht.2])
        exact this.ne
      exact ((Real.continuousAt_log h.ne').inv₀ hlog).neg.continuousWithinAt
  refine intervalIntegral.integrableOn_deriv_of_nonneg hcont ?_ ?_
  · intro t ht
    have ht0 : 0 < t := ht.1
    have hlogneg : Real.log t < 0 := Real.log_neg ht0 (by linarith [ht.2])
    have hlog : Real.log t ≠ 0 := hlogneg.ne
    have h1 : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-t⁻¹ / Real.log t ^ 2)) t :=
      ((Real.hasDerivAt_log ht0.ne').inv hlog).neg
    convert h1 using 1
    rw [abs_of_neg hlogneg]
    field_simp
  · intro t ht
    have := ht.1
    positivity

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnInvMulLogSqNearZeroStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integrableOn_inv_mul_log_sq_near_zero : IntegrableOn (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2) (Set.Ioc 0 (1 / 2)) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_inv_mul_log_sq | exact GlobalTheory.GoodTop.integrableOn_inv_mul_log_sq | (intros; apply GlobalTheory.GoodTop.integrableOn_inv_mul_log_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPoincareAreaDensityPuncturedDisc

section

@[expose] public section

open MeasureTheory Filter Topology

namespace GlobalTheory.GoodTop

theorem integrableOn_poincare_disc :
    IntegrableOn (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) (Metric.closedBall 0 (1 / 2)) := by
  have h := GlobalTheory.T.integrableOn_inv_mul_log_sq_near_zero
  have key : Integrable (fun z : ℂ =>
      (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2) ‖z‖) := by
    rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := (Set.Iic (1 / 2 : ℝ)).indicator (fun t : ℝ => (t * |Real.log t|)⁻¹ ^ 2))]
    have h2 : IntegrableOn ((Set.Iic (1 / 2 : ℝ)).indicator
        (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2)) (Set.Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
        Measure.restrict_restrict measurableSet_Iic, Set.Iic_inter_Ioi]
      exact h
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro t _
    by_cases ht : t ∈ Set.Iic (1 / 2 : ℝ)
    · simp only [Set.indicator_of_mem ht, Complex.finrank_real_complex, smul_eq_mul]
      norm_num
    · simp only [Set.indicator_of_notMem ht, smul_zero]
  rw [← integrable_indicator_iff measurableSet_closedBall]
  refine key.congr (Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ ∈ Set.Iic (1 / 2 : ℝ)
  · have hz' : z ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff]; exact hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
  · have hz' : z ∉ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rw [mem_closedBall_zero_iff]; exact hz
    simp only [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnPoincareAreaDensityPuncturedDiscStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc : IntegrableOn (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2) (Metric.closedBall 0 (1 / 2)) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poincare_disc | exact GlobalTheory.GoodTop.integrableOn_poincare_disc | (intros; apply GlobalTheory.GoodTop.integrableOn_poincare_disc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydi

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_poinVol {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)) (hK : IsCompact K)
    (hS : ∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) :
    IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let g : Fin n → ℂ → ℝ := fun a =>
    if a ∈ S then (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2)
    else (Metric.closedBall (0 : ℂ) R).indicator (fun _ => 1)
  have hg : ∀ a, Integrable (g a) := by
    intro a
    by_cases h : a ∈ S
    · simp only [g, h, if_true]
      exact (integrable_indicator_iff measurableSet_closedBall).2 GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc
    · simp only [g, h, if_false]
      exact (integrable_indicator_iff measurableSet_closedBall).2
        (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _))
  have h1 : Integrable (fun x : Fin n → ℂ => ∏ a, g a (x a)) := Integrable.fintype_prod hg
  have h2 := (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).integrable_comp_of_integrable h1
  refine (h2.integrableOn (s := K)).congr_fun ?_ hK.measurableSet
  intro v hv
  simp only [Function.comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h : a ∈ S
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      simpa using hS v hv a h
    simp only [g, h, if_true, poinWt]
    exact Set.indicator_of_mem this _
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) R := by
      simpa using (PiLp.norm_apply_le v a).trans (hR v hv)
    simp only [g, h, if_false, poinWt, inv_one, one_pow]
    exact Set.indicator_of_mem this _

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydiStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc : ∀ {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)), IsCompact K → (∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poinVol | exact GlobalTheory.GoodTop.integrableOn_poinVol | (intros; apply GlobalTheory.GoodTop.integrableOn_poinVol <;> assumption)
end
end
