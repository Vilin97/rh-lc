module

public import Formalism.TruncatedSeriesCounting.StatementX
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
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColChain
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.FirstSigmaValuationBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.HCoefficientBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KappaSecondExponentBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGIdeal
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGVal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RamifiedValuationInequality
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SaturationCriterion
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubGen
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubSmulOneInjective
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.RingTheory.Ideal.BigOperators

-- Source module: Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ArcExp

section

@[expose] public section

namespace Formalism.TruncatedSeriesCounting.X

theorem arc_exponential_identity : ArcExp := by
  intro r σ κ G j' ell hr hσ hκ hG hj
  have hj' : (j' : ℝ) ≤ ell := by exact_mod_cast hj
  have hjG : (j' : ℝ) * G ≤ ell * G := mul_le_mul_of_nonneg_right hj' hG
  have hell : 0 ≤ (ell : ℝ) * G := mul_nonneg (Nat.cast_nonneg _) hG
  rcases le_total (r + κ) (2 * σ + 2 * j' * G + 1) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

end Formalism.TruncatedSeriesCounting.X
end
end

-- Source module: Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.QNumericalIdentity

section

@[expose] public section

namespace Formalism.TruncatedSeriesCounting.X

theorem q_numerical_identity : QaNum := by
  intro ℓ hℓ H' H eW hH heW
  unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hdiv : ((H' / (ℓ - 1) : ℕ) : ℝ) ≤ (H' : ℝ) / ((ℓ : ℝ) - 1) := by
    have h := Nat.cast_div_le (m := H') (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h
  have hlog : Real.logb ℓ ((H' : ℝ) + 1) ≤ Real.logb ℓ (2 * (H : ℝ)) + 1 := by
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · subst h0
      have h0' : H' = 0 := by omega
      subst h0'
      simp
    · have h1 : (H' : ℝ) + 1 ≤ 2 * H := by
        have h2 : (H' : ℝ) ≤ H := by exact_mod_cast hH
        have h3 : (1 : ℝ) ≤ H := by exact_mod_cast hpos
        linarith
      have h4 := Real.logb_le_logb_of_le hℓ1 (by positivity) h1
      linarith
  have hfrac : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤
      (H : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have heq : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
        (H' : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
      have := hd.ne'
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (pow_pos hd 2).le
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hH) (by linarith)
  push_cast
  linarith

end Formalism.TruncatedSeriesCounting.X
end
end

-- Source module: Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncSig

section

@[expose] public section

namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_signature_bound : TruncSig := by
  unfold TruncSig
  intro ℓ hℓ y X M η
  have hl : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have ha : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have gen : ∀ T : ℝ, 0 ≤ T → (y : ℝ) * ℓ / (ℓ - 1) - max 0 ((ℓ : ℝ) * y - T) ≤ T / (ℓ - 1) := by
    intro T hT
    rw [sub_le_iff_le_add, div_le_iff₀ ha, add_mul, div_mul_cancel₀ _ (ne_of_gt ha)]
    rcases le_total ((ℓ : ℝ) * y - T) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have mono : ∀ T : ℝ, T / ((ℓ : ℝ) - 1) ≤ (T + 1) / ((ℓ : ℝ) - 1) + 1 := by
    intro T
    have h1 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
    rw [add_div]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (gen X (Nat.cast_nonneg _)).trans (mono _)
  · have e : (ℓ : ℝ) * y - η - M = (ℓ : ℝ) * y - (η + M) := by ring
    rw [e]
    have := gen ((η : ℝ) + M) (by positivity)
    have h2 : ((η : ℝ) + M) / (ℓ - 1) ≤ ((M : ℝ) + η) / (ℓ - 1) + 1 := by
      rw [add_comm (η : ℝ)]
      have h3 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
      linarith
    linarith
  · have hsq : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := pow_pos ha 2
    have e : (y : ℝ) * ℓ / (ℓ - 1) = (y : ℝ) * ℓ * (ℓ - 1) / (ℓ - 1) ^ 2 := by
      field_simp
    have key : (y : ℝ) * ℓ / (ℓ - 1) - max 0 (((ℓ : ℝ) - 1) * y - X / ℓ) ≤ X / (ℓ - 1) ^ 2 := by
      rw [e, sub_le_iff_le_add, div_le_iff₀ hsq, add_mul, div_mul_cancel₀ _ (ne_of_gt hsq)]
      have hX : (X : ℝ) = X / ℓ * ℓ := (div_mul_cancel₀ _ hlpos.ne').symm
      rcases le_total (((ℓ : ℝ) - 1) * y - X / ℓ) 0 with h | h
      · rw [max_eq_left h]
        have h4 : ((ℓ : ℝ) - 1) * y * ℓ ≤ X := by
          have h5 : ((ℓ : ℝ) - 1) * y ≤ X / ℓ := by linarith
          have := mul_le_mul_of_nonneg_right h5 hlpos.le
          linarith
        nlinarith
      · rw [max_eq_right h]
        have hs2 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ 2 - ℓ := by nlinarith
        nlinarith [mul_nonneg h hs2]
    have h6 : (0 : ℝ) ≤ 1 := zero_le_one
    linarith

end Formalism.TruncatedSeriesCounting.X
end
end

-- Source module: Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncationRemainderBound

section

@[expose] public section

namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_remainder_bound : TruncRem1 := by
  intro R _ ℓ hℓ π₀ y K c hc
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have hc0 : c = 0 := by push_cast at hc; omega
    subst hc0
    rw [pow_zero]
    exact Ideal.subset_span (Set.mem_insert _ _) |> fun h => by simpa using h
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have e : (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ (y' + 1) =
        π₀ * ((π₀ + (ℓ : R)) + (-(ℓ : R))) ^ y' * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
      rw [show (π₀ + (ℓ : R)) + (-(ℓ : R)) = π₀ by ring, mul_pow, ← pow_mul, pow_succ]
      ring
    rw [e, add_pow (π₀ + (ℓ : R)) (-(ℓ : R)) y', Finset.mul_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hm' : m ≤ y' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    by_cases hj : c ≤ y' - m
    · have h1 : (-(ℓ : R)) ^ (y' - m) = (ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) := by
        have hsplit : (ℓ : R) ^ (y' - m) = (ℓ : R) ^ c * (ℓ : R) ^ (y' - m - c) := by
          rw [← pow_add]
          congr 1
          omega
        rw [neg_pow, hsplit]
        ring
      have hmem : (ℓ : R) ^ c ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [h1]
      have : π₀ * ((π₀ + ↑ℓ) ^ m * ((ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))) * ↑(y'.choose m)) *
          (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = (ℓ : R) ^ c * (π₀ * (π₀ + ↑ℓ) ^ m * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) *
          ↑(y'.choose m) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1))) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem
    · have hK : K ≤ m + (ℓ - 1) * (y' + 1) := by
        push_neg at hj
        have h2 : (c : ℤ) ≤ (ℓ : ℤ) * ((y' + 1 : ℕ) : ℤ) - K := hc
        push_cast at h2
        have h3 : (c : ℤ) ≥ (y' : ℤ) - m + 1 := by omega
        zify [hℓ]
        nlinarith [h2, h3]
      have hmem : π₀ * (π₀ + (ℓ : R)) ^ K ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have : π₀ * ((π₀ + ↑ℓ) ^ m * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) =
          π₀ * (π₀ + (ℓ : R)) ^ K * ((π₀ + ↑ℓ) ^ (m + (ℓ - 1) * (y' + 1) - K) * (-(ℓ : R)) ^ (y' - m) *
            ↑(y'.choose m)) := by
        have e2 : (π₀ + (ℓ : R)) ^ K * (π₀ + (ℓ : R)) ^ (m + (ℓ - 1) * (y' + 1) - K) =
            (π₀ + (ℓ : R)) ^ m * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hK]
        linear_combination (π₀ * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * e2.symm
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem

end Formalism.TruncatedSeriesCounting.X
end
end

-- Source module: Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.UnitCoefficientPowerMod

section

@[expose] public section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.X

open PowerSeries

theorem unit_coefficient_power_mod : UnitCoefficientPowerMod := by
  intro O _ ℓ ε u y
  have hsplit : ∃ W : PowerSeries O,
      (Formalism.WindowSums.p1 ℓ ε u) ^ y = (u * X ^ ℓ) ^ y + C (ℓ : O) * W := by
    obtain ⟨V, hV⟩ := sub_dvd_pow_sub_pow (Formalism.WindowSums.p1 ℓ ε u) (u * X ^ ℓ) y
    refine ⟨ε * V, ?_⟩
    have : Formalism.WindowSums.p1 ℓ ε u - u * X ^ ℓ = C (ℓ : O) * ε := by unfold Formalism.WindowSums.p1; ring
    rw [this] at hV
    linear_combination hV
  obtain ⟨W, hW⟩ := hsplit
  have hc : coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) =
      constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W := by
    rw [hW, map_add (f := _), coeff_C_mul, mul_pow, ← pow_mul, mul_comm ℓ y]
    have := coeff_mul_X_pow (u ^ y) (y * ℓ) 0
    rw [zero_add] at this
    rw [this, coeff_zero_eq_constantCoeff, map_pow]
  refine ⟨?_, ?_⟩
  · rw [hc, add_sub_cancel_left, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
  · intro hloc hℓ hu
    rw [hc]
    have h0 : IsUnit (constantCoeff u ^ y) := (hu.map constantCoeff).pow y
    have h1 : (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hℓ)
    by_contra hne
    have h2 : constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hne
    have h3 := Ideal.sub_mem _ h2 h1
    rw [add_sub_cancel_right] at h3
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) h0

end Formalism.TruncatedSeriesCounting.X
end
end
end

-- Source module: Formalism.TruncatedSeriesCounting.EtaDeterminantPolynomialIdentities

section

@[expose] public section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

end Formalism.TruncatedSeriesCounting.WachCoordinates

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

theorem ramified_coefficient_chain_bounds : HCoef ∧ ExpBound ∧ MaxZeroExponentInequality ∧ TwoIntervalValuationSumBound ∧ LemmaGVal ∧ LemmaGIdeal ∧ RamifiedValuationInequality ∧ LenPi0 ∧ ColChain ∧ SubGen ∧ ColAssembly :=
  ⟨h_coefficient_bound, expBound_statement, second_exponent_bound, first_sigma_valuation_bound, g_coeff_valuation_statement, g_ideal_valuation_statement, ramified_valuation_inequality, length_pi_zero_bound, column_chain_bound, submodule_generator_count, column_assembly_bound⟩

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

namespace Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

end Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

namespace Formalism.TruncatedSeriesCounting.R9

end Formalism.TruncatedSeriesCounting.R9

namespace Formalism.TruncatedSeriesCounting.X

theorem pX_conditions : QaNum ∧ TruncSig ∧ TruncRem1 ∧ ArcExp ∧ SatA ∧ UnitCoefficientPowerMod :=
  ⟨q_numerical_identity, truncation_signature_bound, truncation_remainder_bound, arc_exponential_identity, saturation_criterion, unit_coefficient_power_mod⟩

end Formalism.TruncatedSeriesCounting.X
end
end
