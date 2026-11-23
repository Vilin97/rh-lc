module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpQuadraticLowerAndLogLinearLower

section

@[expose] public section

open Matrix Finset Real

namespace GlobalTheory

theorem one_add_add_sq_div_three_le_exp (u : ℝ) (hu : |u| ≤ 1) :
    1 + u + u ^ 2 / 3 ≤ Real.exp u := by
  have h := Real.exp_bound hu (n := 5) (by norm_num)
  have h1 := (abs_le.mp h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
  norm_num at h1
  have h4 : |u| ^ 4 = u ^ 4 := by
    rw [← abs_pow]; exact abs_of_nonneg (by positivity)
  have h5 : |u| ^ 5 ≤ u ^ 4 := by
    rw [← h4, pow_succ]
    exact mul_le_of_le_one_right (by positivity) hu
  have h6 : -1 ≤ u := (abs_le.mp hu).1
  have h7 : 0 ≤ u ^ 2 * (1 + u) := mul_nonneg (sq_nonneg u) (by linarith)
  have h8 : 0 ≤ u ^ 4 := by positivity
  nlinarith

theorem three_mul_div_four_le_log_one_add (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 3) :
    3 * u / 4 ≤ Real.log (1 + u) := by
  have hp : 0 < 1 + u := by linarith
  refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hp)
  have : (1 + u)⁻¹ ≤ 1 - 3 * u / 4 := by
    rw [inv_eq_one_div, div_le_iff₀ hp]
    nlinarith
  linarith

theorem exp_quadratic_lower_and_log_linear_lower :
    (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) :=
  ⟨one_add_add_sq_div_three_le_exp, three_mul_div_four_le_log_one_add⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpQuadraticLowerAndLogLinearLowerStatement

section

@[expose] public section

open Matrix Finset Real

theorem _root_.GlobalTheory.T.exp_quadratic_lower_and_log_linear_lower' : (∀ u : ℝ, |u| ≤ 1 → 1 + u + u ^ 2 / 3 ≤ Real.exp u) ∧ ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 3 → 3 * u / 4 ≤ Real.log (1 + u) := by
  first | exact @GlobalTheory.exp_quadratic_lower_and_log_linear_lower | exact GlobalTheory.exp_quadratic_lower_and_log_linear_lower | (intros; apply GlobalTheory.exp_quadratic_lower_and_log_linear_lower <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CumulantLowerBoundOfBoundedCentred

section

@[expose] public section

open Matrix Finset Real

namespace GlobalTheory

theorem cumulant_lower_bound_of_bounded_centred :
    ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 →
      ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) →
      min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  intro ι _ w y R hR hw hs hm hb
  obtain ⟨hexp, hlog⟩ := GlobalTheory.T.exp_quadratic_lower_and_log_linear_lower'
  set t : ℝ := min 1 (1 / R) with ht
  set V : ℝ := ∑ J, w J * y J ^ 2 with hV
  set S : ℝ := ∑ J, w J * Real.exp (y J) with hS
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htR : t * R ≤ 1 := by
    have : t ≤ 1 / R := min_le_right _ _
    rwa [le_div_iff₀ hR] at this
  have hty : ∀ J, w J ≠ 0 → |t * y J| ≤ 1 := by
    intro J hJ
    rw [abs_mul, abs_of_pos ht0]
    exact (mul_le_mul_of_nonneg_left (hb J hJ) ht0.le).trans htR
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun J _ => mul_nonneg (hw J) (sq_nonneg _)
  have htV : t ^ 2 * V ≤ 1 := by
    rw [hV, Finset.mul_sum, ← hs]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · have h1 : (t * y J) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hty J hJ)
      have := mul_le_mul_of_nonneg_left h1 (hw J)
      nlinarith
  have hlow : 1 + t ^ 2 * V / 3 ≤ ∑ J, w J * Real.exp (t * y J) := by
    have e : 1 + t ^ 2 * V / 3 = ∑ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3) := by
      have e2 : ∀ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3)
          = w J + t * (w J * y J) + t ^ 2 / 3 * (w J * y J ^ 2) := fun J => by ring
      simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, hs, hm]
      rw [← hV]; ring
    rw [e]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · exact mul_le_mul_of_nonneg_left (hexp _ (hty J hJ)) (hw J)
  have hS1 : 1 ≤ S := by
    have : ∑ J, w J * (y J + 1) = 1 := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hs, hm, zero_add]
    rw [← this]
    exact Finset.sum_le_sum fun J _ =>
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hw J)
  have hS0 : 0 < S := by linarith
  set F : ℝ := Real.log S with hF
  have hEF : Real.exp F = S := Real.exp_log hS0
  have hpt : ∀ J, Real.exp (t * y J)
      ≤ Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t)) := by
    intro J
    have h := convexOn_exp.2 (Set.mem_univ (y J - F)) (Set.mem_univ 0) ht0.le
      (sub_nonneg.2 ht1) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
    rw [Real.exp_sub, hEF] at h
    have e : t * y J = t * F + t * (y J - F) := by ring
    rw [e, Real.exp_add]
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hup : ∑ J, w J * Real.exp (t * y J) ≤ Real.exp (t * F) := by
    calc ∑ J, w J * Real.exp (t * y J)
        ≤ ∑ J, w J * (Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t))) :=
          Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left (hpt J) (hw J)
      _ = ∑ J, (Real.exp (t * F) * t / S * (w J * Real.exp (y J))
            + Real.exp (t * F) * (1 - t) * w J) :=
          Finset.sum_congr rfl fun J _ => by ring
      _ = Real.exp (t * F) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, ← hS]
          field_simp
          ring
  have hu0 : 0 ≤ t ^ 2 * V / 3 := by positivity
  have h1 := hlog (t ^ 2 * V / 3) hu0 (by linarith)
  have h2 : Real.log (1 + t ^ 2 * V / 3) ≤ t * F := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hlow.trans hup
  have h3 : t * (t * V / 4) ≤ t * F := by nlinarith
  exact le_of_mul_le_mul_left h3 ht0

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CumulantLowerBoundOfBoundedCentredStatement

section

@[expose] public section

open Matrix Finset Real

theorem _root_.GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred : ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 → ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) → min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  first | exact @GlobalTheory.cumulant_lower_bound_of_bounded_centred | exact GlobalTheory.cumulant_lower_bound_of_bounded_centred | (intros; apply GlobalTheory.cumulant_lower_bound_of_bounded_centred <;> assumption)
end
end
