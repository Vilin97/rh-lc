module

public import Formalism.ThetaSupremumBounds.StatementA
public import Formalism.ThetaSupremumBounds.GaussianShiftBounds.BlockIntegralOf
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Linter.Style
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

-- Source module: Formalism.ThetaSupremumBounds.GaussianShiftBounds.HeightsoundOf

section

@[expose] public section

open Finset MeasureTheory
open scoped ComplexConjugate Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

theorem blockBound_of (hF : FockJet) (hI : BlockIntegral) : BlockBound := by
  intro Pl ι _ _ W _ _ _ r ν n s Th c Rc lam Om S hν hνn hs hsq hTc hTs hTb hsupp hR hOm hlam
  have hB := hI Pl ι W r ν s Th (fun u => Rc.sum (fun e A => mono (cj u) e • A)) S hν hs hsq hTb hR
  have hJ := hF (Pl × ι) Th c S hTc hTs hTb
  have h1 : ∀ e (u : Pl × ι → ℂ), (Th u * (Real.exp (-(nsq u)) : ℂ)) • mono (cj u) e • Rc e =
      (Th u * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ)) • Rc e := fun e u => by
    rw [smul_smul]; congr 1; ring
  have hint : ∫ u : Pl × ι → ℂ, (Th u * (Real.exp (-(nsq u)) : ℂ)) • Rc.sum (fun e A => mono (cj u) e • A) =
      (π : ℂ) ^ (Fintype.card Pl * Fintype.card ι) • Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) := by
    simp only [Finsupp.sum, Finset.smul_sum]
    simp_rw [h1]
    rw [MeasureTheory.integral_finsetSum _ fun e _ => (hJ e).1.smul_const (Rc e)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [integral_smul_const, (hJ e).2, Fintype.card_prod, smul_smul]
  have hP : Rc.sum (fun e A => (c e * (mfact e : ℂ) * ∏ x : Pl × ι, lam x.1 ^ e x) • A) =
      (∏ τ, lam τ ^ n τ) • Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) := by
    simp only [Finsupp.sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have hl : ∏ x : Pl × ι, lam x.1 ^ e x = ∏ τ, lam τ ^ n τ := by
      simp only [Fintype.prod_prod_type, Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl fun τ _ => by rw [hsupp e he τ]
    rw [hl, smul_smul, mul_comm (∏ τ, lam τ ^ n τ)]
  set X := Rc.sum (fun e A => (c e * (mfact e : ℂ)) • A) with hXdef
  have hpi : (0 : ℝ) < π ^ (Fintype.card Pl * Fintype.card ι) := by positivity
  have hX : ‖X‖ ≤ S * ∏ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
      Real.exp ((∑ i, ph (ν τ i)) / 2)) := by
    rw [hint, norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      mul_div_cancel_left₀ _ hpi.ne'] at hB
    simpa only [hνn] using hB
  have e1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have e2 : ∀ x : ℝ, Real.exp (x / 2) ^ 2 = Real.exp x := fun x => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hY : ∀ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
      Real.exp ((∑ i, ph (ν τ i)) / 2)) ^ 2 = Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) *
      Real.exp (∑ i, ph (ν τ i)) := fun τ => by
    rw [mul_pow, mul_pow, e1, e2, ← pow_mul, mul_comm (Fintype.card ι) 2]
  have hS : ‖X‖ ^ 2 ≤ S ^ 2 * ∏ τ, (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) *
      Real.exp (∑ i, ph (ν τ i))) := by
    have h2 : ‖X‖ ^ 2 ≤ (S * ∏ τ, (Real.exp (1 / 2) * (2 * (n τ : ℝ) + 2) ^ Fintype.card ι *
        Real.exp ((∑ i, ph (ν τ i)) / 2))) ^ 2 := by gcongr
    rwa [mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl fun τ _ => hY τ] at h2
  have hL : ‖∏ τ, lam τ ^ n τ‖ ^ 2 = ∏ τ, (Om τ)⁻¹ ^ n τ := by
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [norm_pow, ← pow_mul, mul_comm, pow_mul, hlam]
  rw [hP, norm_smul, mul_pow, hL, Finset.prod_mul_distrib, mul_left_comm (S ^ 2)]
  exact mul_le_mul_of_nonneg_left hS
    (Finset.prod_nonneg fun τ _ => pow_nonneg (inv_nonneg.2 (hOm τ).le) _)

end Formalism.DimensionVariation
end
end

-- Source module: Formalism.ThetaSupremumBounds.GaussianShiftBounds.GaussCoord

section

@[expose] public section

open Finset MeasureTheory
open scoped ComplexConjugate Real

namespace Formalism.DimensionVariation

private theorem integral_complex_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2)) = π / c := by
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc ∫ z : ℂ, Real.exp (-(c * ‖z‖ ^ 2))
      = ∫ z : ℂ, (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
          (Complex.measurableEquivRealProd z) := by
        congr 1
        funext z
        show Real.exp (-(c * ‖z‖ ^ 2)) = Real.exp (-c * z.re ^ 2) * Real.exp (-c * z.im ^ 2)
        rw [← Real.exp_add, hsq]
        congr 1
        ring
    _ = ∫ p : ℝ × ℝ, Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2) := by
        exact Complex.volume_preserving_equiv_real_prod.integral_comp'
          (fun p : ℝ × ℝ => Real.exp (-c * p.1 ^ 2) * Real.exp (-c * p.2 ^ 2))
    _ = (∫ x : ℝ, Real.exp (-c * x ^ 2)) * ∫ y : ℝ, Real.exp (-c * y ^ 2) :=
        integral_prod_mul (fun x : ℝ => Real.exp (-c * x ^ 2)) (fun y : ℝ => Real.exp (-c * y ^ 2))
    _ = π / c := by
        rw [integral_gaussian]
        exact Real.mul_self_sqrt (div_nonneg Real.pi_pos.le hc.le)

theorem gaussianIntegralDiagonal : GaussCoord := by
  intro κ hκ b hb
  have hint_r : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = ∏ x, π / b x := by
    calc ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2)
        = ∫ u : κ → ℂ, ∏ x, Real.exp (-(b x * ‖u x‖ ^ 2)) := by
          congr 1
          funext u
          rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ = ∏ x, ∫ z : ℂ, Real.exp (-(b x * ‖z‖ ^ 2)) := by
          exact MeasureTheory.integral_fintype_prod_volume_eq_prod
            (fun x (z : ℂ) => Real.exp (-(b x * ‖z‖ ^ 2)))
      _ = ∏ x, π / b x :=
          Finset.prod_congr rfl fun x _ => integral_complex_exp_neg_mul_sq_norm (hb x)
  refine ⟨?_, hint_r⟩
  by_contra hni
  have h0 : ∫ u : κ → ℂ, Real.exp (-∑ x, b x * ‖u x‖ ^ 2) = 0 := integral_undef hni
  rw [hint_r] at h0
  exact (Finset.prod_ne_zero_iff.mpr fun x _ => div_ne_zero Real.pi_ne_zero (hb x).ne') h0

theorem blockIntegralBound : BlockIntegral :=
  blockIntegral_of gaussianIntegralDiagonal

theorem blockBound_of_fockJet (hF : FockJet) : BlockBound :=
  blockBound_of hF blockIntegralBound

end Formalism.DimensionVariation
end
end
