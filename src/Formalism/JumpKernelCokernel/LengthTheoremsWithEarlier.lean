module

public import Formalism.EisensteinCokernelLengths.ExponentChainBound
public import Formalism.JumpKernelCokernel.KerCokerEq
public import Formalism.JumpKernelCokernel.LemmaDJoint
public import Formalism.JumpKernelCokernel.Statement
public import Formalism.TruncatedSeriesCounting.LengthQuotientLeOfPowSMul
public import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.DistinguishedPowMemSpanOfTrichotomy
public import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.PadicValNatFactorialLeReal
public import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.RationalTailBoundCubic
public import Formalism.JumpKernelCokernel.JumpShiftProofs.CokerTors
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly
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
import Mathlib.Order.CompletePartialOrder
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
import Formalism.JumpKernelCokernel.JumpShiftProofs.DetLen
public import Formalism.JumpKernelCokernel.JumpShiftProofs.ExpRowD
public import Formalism.JumpKernelCokernel.JumpShiftProofs.HCoefLim
public import Formalism.JumpKernelCokernel.JumpShiftProofs.InvConst
public import Formalism.JumpKernelCokernel.JumpShiftProofs.KerCoker
public import Formalism.JumpKernelCokernel.JumpShiftProofs.KerCokerEq
public import Formalism.JumpKernelCokernel.JumpShiftProofs.LemmaDJoint
import Formalism.JumpKernelCokernel.JumpShiftProofs.LenSplit
public import Formalism.JumpKernelCokernel.JumpShiftProofs.PdFacts
public import Formalism.JumpKernelCokernel.JumpShiftProofs.PowBinom
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncZero
public import Formalism.JumpKernelCokernel.JumpShiftProofs.RowDJoint
public import Formalism.JumpKernelCokernel.JumpShiftProofs.ThickA
public import Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB
public import Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKer
public import Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKerSum
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.CancelQ
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColAssembly
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ColChain
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ExpBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.FirstSigmaValuationBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.HCoefficientBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.KappaSecondExponentBound
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGIdeal
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGVal
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LengthQuotientLeOfPowSMul
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RamifiedValuationInequality
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubGen
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SubSmulOneInjective
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncZero

-- Source module: Formalism.JumpKernelCokernel.JumpShiftProofs.ColThmC

section

@[expose] public section

noncomputable section

namespace Formalism.KernelCokernelLengths

theorem column_theorem_C : ColThmC := by
  intro O _ _ _ M _ _ _ _ ℓ P k F gen n r m e e' S cD hn hrk hgen hk hF0 hF hsub hG hN hE
  have h := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.column_assembly_bound O M ℓ P k F gen m e e' (r * S + 2 * m * cD) hF0 hF hsub hG hN hE
  refine h.trans ?_
  have hAB : Module.finrank O M * e + gen.card * m * e' + (k - gen.card) * (r * S + 2 * m * cD) ≤
      (n + 1) * r * e + 4 * n * m * e' + (3 * n / 2) * (r * S + 2 * m * cD) := by
    gcongr
  gcongr

end Formalism.KernelCokernelLengths
end
end
end

-- Source module: Formalism.JumpKernelCokernel.JumpShiftProofs.ColumnDegreeBound

section

@[expose] public section

namespace Formalism.KernelCokernelLengths

theorem column_degree_bound : CDge := by
  intro ℓ hℓ bi S η h hh
  have h2 : bi + S + η ≤ h + η := by omega
  gcongr
  all_goals first
    | exact_mod_cast h2
    | (rw [sub_nonneg]; exact_mod_cast (by omega : 1 ≤ ℓ))
    | (rw [sub_pos]; exact_mod_cast (by omega : 1 < ℓ))

end Formalism.KernelCokernelLengths
end
end

-- Source module: Formalism.JumpKernelCokernel.JumpShiftProofs.FiltrationExponentHolds

section

@[expose] public section

theorem Formalism.KernelCokernelLengths.filtration_exponent_holds : Formalism.KernelCokernelLengths.FExp := by
  intro R _ u π₀ q ℓ hℓ Mi h hMi
  set m := h / (ℓ - 1) with hm
  have hpos : 0 < ℓ - 1 := by omega
  have hk : Mi + 1 ≤ (ℓ - 1) * (m + 1) := by
    have := Nat.lt_mul_div_succ h hpos
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hMi this)
  obtain ⟨d, hd⟩ : ∃ d, (ℓ - 1) * (m + 1) = Mi + 1 + d := ⟨_, (Nat.add_sub_cancel' hk).symm⟩
  rw [Ideal.mem_span_singleton]
  refine ⟨u ^ (m + 1) * q ^ d, ?_⟩
  rw [mul_pow, mul_pow, ← pow_mul, hd, pow_add]
  ring
end
end

-- Source module: Formalism.JumpKernelCokernel.JumpShiftProofs.IdealPowerSumMem

section

@[expose] public section

namespace Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem add_pow_mem_span_pow_pow (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ) :
    (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := by
  have hπ : π₀ ^ A ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := Ideal.subset_span (Set.mem_insert _ _)
  have hℓ : ℓ ^ r ∈ Ideal.span {π₀ ^ A, ℓ ^ r} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [add_pow]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ A + r - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hA : A ≤ i
  · have e : π₀ ^ i = π₀ ^ A * π₀ ^ (i - A) := by rw [← pow_add, Nat.add_sub_cancel' hA]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ))
  · have hr : r ≤ A + r - 1 - i := by omega
    have e : ℓ ^ (A + r - 1 - i) = ℓ ^ r * ℓ ^ (A + r - 1 - i - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hℓ))

end Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem Formalism.KernelCokernelLengths.ideal_power_sum_mem : Formalism.KernelCokernelLengths.QPow := by
  intro R _ π₀ ℓ A r
  exact Formalism.KernelCokernelLengths.IdealPowerSumLemmas.add_pow_mem_span_pow_pow R π₀ ℓ A r
end
end

-- Source module: Formalism.JumpKernelCokernel.JumpShiftProofs.JumpShift

section

@[expose] public section

namespace Formalism.KernelCokernelLengths

theorem jump_shift_holds : JumpShift := by
  intro s S η t a ht
  refine ⟨fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

end Formalism.KernelCokernelLengths
end
end

-- Source module: Formalism.JumpKernelCokernel.JumpShiftProofs.RelZero

section

@[expose] public section

namespace Formalism.KernelCokernelLengths

theorem relation_vanishes : RelZero := by
  intro R _ u π₀ q ℓ h η y hℓ hη hy
  apply Formalism.TruncatedSeriesCounting.R9.pow_mem_span_pow_mul R u π₀ q ℓ (h / (ℓ - 1) + 1) η y hy
  have hpos : 0 < ℓ - 1 := by omega
  have h1 : h < (ℓ - 1) * (h / (ℓ - 1) + 1) := Nat.lt_mul_div_succ h hpos
  have h2 : (ℓ - 1) * (h / (ℓ - 1) + 1) ≤ (ℓ - 1) * y := Nat.mul_le_mul_left _ hy
  omega

end Formalism.KernelCokernelLengths
end
end

-- Source module: Formalism.JumpKernelCokernel.JumpShiftProofs.RowDegreeBound

section

@[expose] public section

namespace Formalism.KernelCokernelLengths

theorem row_degree_bound : RowD := by
  unfold RowD
  intro h h1 η hη
  have key : 32 * (h1 + η) ≤ 50 * h1 := by omega
  gcongr ?_ / _
  exact_mod_cast key

end Formalism.KernelCokernelLengths
end
end

-- Source module: Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.CancelC

section

@[expose] public section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

open PowerSeries

theorem mem_span_of_C_pow_mul : CancelC := by
  intro O _ _ a v t b g ha hvt hg
  rw [Ideal.mem_span_pair] at hg ⊢
  obtain ⟨p, q, hpq⟩ := hg
  have hdiv : (X : PowerSeries O) ^ b ∣ g - p * C (a ^ (t - v)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have h1 := congrArg (PowerSeries.coeff n) hpq
    simp only [map_add (f := _), PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      if_neg (show ¬ b ≤ n by omega), add_zero] at h1
    rw [map_sub, PowerSeries.coeff_mul_C, sub_eq_zero]
    apply mul_left_cancel₀ (pow_ne_zero v ha)
    rw [← h1]
    have ht : a ^ t = a ^ v * a ^ (t - v) := by rw [← pow_add, Nat.add_sub_cancel' hvt]
    rw [ht]
    ring
  obtain ⟨r, hr⟩ := hdiv
  exact ⟨p, r, by linear_combination (-1 : PowerSeries O) * hr⟩

end Formalism.TruncatedSeriesCounting.R9
end
end
end

-- Source module: Formalism.JumpKernelCokernel.LengthTheoremsWithEarlier

section

@[expose] public section

namespace Formalism.KernelCokernelLengths

theorem length_theorems_all_hold : Formalism.KernelCokernelLengths.DetLen ∧ Formalism.KernelCokernelLengths.RelZero ∧ Formalism.KernelCokernelLengths.CDge ∧ Formalism.KernelCokernelLengths.RowD ∧ Formalism.KernelCokernelLengths.ExpRowD ∧ Formalism.KernelCokernelLengths.InvConst ∧ Formalism.KernelCokernelLengths.KerCoker ∧ Formalism.KernelCokernelLengths.JumpShift ∧ Formalism.KernelCokernelLengths.PowBinom ∧ Formalism.KernelCokernelLengths.HCoefLim ∧ Formalism.KernelCokernelLengths.QPow ∧ Formalism.KernelCokernelLengths.ColThmC ∧ Formalism.KernelCokernelLengths.FExp ∧ Formalism.KernelCokernelLengths.ThickB ∧ Formalism.KernelCokernelLengths.KerCokerEq ∧ Formalism.KernelCokernelLengths.CokerSurj ∧ Formalism.KernelCokernelLengths.ThickA ∧ Formalism.KernelCokernelLengths.PdFacts ∧ Formalism.KernelCokernelLengths.LenSplit ∧ Formalism.KernelCokernelLengths.TorsKerSum ∧ Formalism.KernelCokernelLengths.TorsKer ∧ Formalism.KernelCokernelLengths.RowDJoint ∧ Formalism.KernelCokernelLengths.LemmaDJoint ∧ Formalism.KernelCokernelLengths.CokerTors := by
  exact ⟨determinant_length_formula, relation_vanishes, column_degree_bound, row_degree_bound, row_degree_exponent, exists_fixed_add_of_sub_mem, kernel_cokernel_lengths, jump_shift_holds, power_binomial_bound, coefficient_height_limit, ideal_power_sum_mem, column_theorem_C, filtration_exponent_holds, thickness_second_bound, endKernelCokernelLengthEq, cokernelLengthLeOfSurjective, thickness_first_bound, polynomial_degree_facts, length_splits_additively, torsion_kernel_sum_length, torsion_kernel_length, row_degree_joint_form, lemma_D_joint_form, cokernel_torsion_holds⟩

theorem length_theorems_with_earlier :
    (Formalism.KernelCokernelLengths.DetLen ∧ Formalism.KernelCokernelLengths.RelZero ∧ Formalism.KernelCokernelLengths.CDge ∧ Formalism.KernelCokernelLengths.RowD ∧ Formalism.KernelCokernelLengths.ExpRowD ∧ Formalism.KernelCokernelLengths.InvConst ∧ Formalism.KernelCokernelLengths.KerCoker ∧ Formalism.KernelCokernelLengths.JumpShift ∧ Formalism.KernelCokernelLengths.PowBinom ∧ Formalism.KernelCokernelLengths.HCoefLim ∧ Formalism.KernelCokernelLengths.QPow ∧ Formalism.KernelCokernelLengths.ColThmC ∧ Formalism.KernelCokernelLengths.FExp ∧ Formalism.KernelCokernelLengths.ThickB ∧ Formalism.KernelCokernelLengths.KerCokerEq ∧ Formalism.KernelCokernelLengths.CokerSurj ∧ Formalism.KernelCokernelLengths.ThickA ∧ Formalism.KernelCokernelLengths.PdFacts ∧ Formalism.KernelCokernelLengths.LenSplit ∧ Formalism.KernelCokernelLengths.TorsKerSum ∧ Formalism.KernelCokernelLengths.TorsKer ∧ Formalism.KernelCokernelLengths.RowDJoint ∧ Formalism.KernelCokernelLengths.LemmaDJoint ∧ Formalism.KernelCokernelLengths.CokerTors) ∧
    (Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.HCoef ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ExpBound ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.MaxZeroExponentInequality ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.TwoIntervalValuationSumBound ∧
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.LemmaGVal ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.LemmaGIdeal ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.RamifiedValuationInequality ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.LenPi0 ∧
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ColChain ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.SubGen ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ColAssembly) ∧
    (Formalism.TruncatedSeriesCounting.R9.LengthQuotientLeOfPowSMul ∧ Formalism.TruncatedSeriesCounting.R9.CancelQ ∧ Formalism.TruncatedSeriesCounting.R9.CancelC ∧ Formalism.TruncatedSeriesCounting.R9.TruncZero) ∧
    (Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.FirstRelationTorsion ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.FirstRelationModule ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.SecondRelationTorsion ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.GapG ∧
      Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.RRVal ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.ExponentChainBound ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.NumC) := by
  exact ⟨length_theorems_all_hold, ⟨Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.h_coefficient_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.expBound_statement, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.second_exponent_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.first_sigma_valuation_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.g_coeff_valuation_statement, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.g_ideal_valuation_statement, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_valuation_inequality, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.length_pi_zero_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.column_chain_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.submodule_generator_count, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.column_assembly_bound⟩, ⟨Formalism.TruncatedSeriesCounting.R9.length_quotient_le_of_pow_smul, Formalism.TruncatedSeriesCounting.R9.mem_span_of_X_pow_mul, Formalism.TruncatedSeriesCounting.R9.mem_span_of_C_pow_mul, Formalism.TruncatedSeriesCounting.R9.pow_mem_span_pow_mul⟩, ⟨Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.linearFactorPowMemSpan, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.linearFactorPowMemSpanXPow, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.distinguishedPowMemSpan, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.gapG_proof, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.rRVal_proof, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.exponentChainBound, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.rationalTailBoundCubic⟩⟩

end Formalism.KernelCokernelLengths
end
end
