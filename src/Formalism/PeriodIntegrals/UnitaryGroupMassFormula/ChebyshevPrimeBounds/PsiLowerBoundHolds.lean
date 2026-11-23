module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PrimeCountBoundOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.LogFactorialEqSumOfLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.LogFactorialLe

section

@[expose] public section

noncomputable section

namespace PI.PC

open Finset Real
open scoped Nat

theorem g_diff {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * log a ≤ (b * log b - b) - (a * log a - a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h
  have h2 : b - a ≤ b * (log b - log a) := by
    have h3 := mul_le_mul_of_nonneg_left h hb.le
    rwa [mul_sub, mul_one, mul_div_cancel₀ _ hb.ne'] at h3
  have e : (b * log b - b) - (a * log a - a) - (b - a) * log a = b * (log b - log a) - (b - a) := by
    ring
  linarith

theorem g_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : a * log a - a ≤ b * log b - b := by
  have h := g_diff (by linarith : (0 : ℝ) < a) hab
  have hl : 0 ≤ (b - a) * log a := mul_nonneg (by linarith) (Real.log_nonneg ha)
  linarith

theorem third_le_log : (1 : ℝ) / 3 ≤ log (3 / 2) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  calc (1 : ℝ) / 3 = 1 - (3 / 2)⁻¹ := by norm_num
    _ ≤ log (3 / 2) := h

theorem h_mono {a b : ℝ} (ha : 3 / 2 ≤ a) (hab : a ≤ b) :
    a * log a - a - log a / 2 ≤ b * log b - b - log b / 2 := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hg := g_diff ha0 hab
  have hlog : log b - log a ≤ (b - a) / a := by
    have h := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at h
    rwa [show b / a - 1 = (b - a) / a by field_simp] at h
  have hla : 1 / 3 ≤ log a := le_trans third_le_log (Real.log_le_log (by norm_num) ha)
  have h3 : (b - a) / a ≤ (b - a) * (2 / 3) := by
    rw [div_le_iff₀ ha0]
    nlinarith
  have h4 : (b - a) * (1 / 3) ≤ (b - a) * log a := mul_le_mul_of_nonneg_left hla (by linarith)
  linarith

theorem h_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : 2 ≤ b) :
    a * log a - a - log a / 2 ≤ b * log b - b - log b / 2 := by
  by_cases ha' : 3 / 2 ≤ a
  · exact h_mono ha' hab
  push_neg at ha'
  have hb2 := h_mono (a := 2) (b := b) (by norm_num) hb
  have hla : log a ≤ a - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hq : (a - 1 / 2) * log a ≤ (a - 1 / 2) * (a - 1) :=
    mul_le_mul_of_nonneg_left hla (by linarith)
  have hq2 : (a - 1 / 2) * (a - 1) - a ≤ -1 := by nlinarith
  have h2 : -1 ≤ 2 * log 2 - 2 - log 2 / 2 := by
    have := Real.log_two_gt_d9
    linarith
  have e : (a - 1 / 2) * log a = a * log a - log a / 2 := by ring
  linarith

theorem log_factorial_le {n : ℕ} (hn : n ≠ 0) :
    log ((n ! : ℕ) : ℝ) ≤ n * log n - n + log n / 2 + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h1 : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  have hpos := Stirling.stirlingSeq'_pos m
  have h2 := Real.log_le_log hpos h1
  rw [Stirling.log_stirlingSeq_formula, Stirling.stirlingSeq_one,
    Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at h2
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [Real.log_mul (by norm_num) hm.ne', Real.log_div hm.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at h2
  push_cast at h2 ⊢
  nlinarith [h2]

theorem log_two_pi_ge : (9 : ℝ) / 5 ≤ log (2 * π) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have he := Real.exp_one_lt_d9
  have h15 : (6 : ℝ) / 5 ≤ Real.exp (1 / 5) := by
    have := Real.add_one_le_exp (1 / 5 : ℝ)
    linarith
  have hsplit : Real.exp (9 / 5) * Real.exp (1 / 5) = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have hpi := Real.pi_gt_d2
  have hpos : 0 < Real.exp (9 / 5) := Real.exp_pos _
  have he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 :=
    mul_self_lt_mul_self (Real.exp_pos 1).le he
  have h3 : Real.exp (9 / 5) * (6 / 5) ≤ Real.exp (9 / 5) * Real.exp (1 / 5) :=
    mul_le_mul_of_nonneg_left h15 hpos.le
  nlinarith

theorem log_thirty_ge : (33 : ℝ) / 10 ≤ log 30 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have he := Real.exp_one_lt_d9
  have hsplit : Real.exp (33 / 10) = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    norm_num
  have hm : Real.exp (3 / 10) * Real.exp (-3 / 10) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h1 : (7 : ℝ) / 10 ≤ Real.exp (-3 / 10) := by
    have := Real.add_one_le_exp (-3 / 10 : ℝ)
    linarith
  have h310 : Real.exp (3 / 10) ≤ 10 / 7 := by
    have hp := Real.exp_pos (3 / 10)
    nlinarith
  have he2 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 :=
    mul_self_lt_mul_self (Real.exp_pos 1).le he
  have he3 : Real.exp 1 * Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 * 2.7182818286 :=
    mul_lt_mul'' he2 he (by positivity) (Real.exp_pos 1).le
  rw [hsplit]
  have h4 : Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (3 / 10) ≤
      (2.7182818286 * 2.7182818286 * 2.7182818286) * (10 / 7) :=
    mul_le_mul he3.le h310 (Real.exp_pos _).le (by norm_num)
  linarith

theorem lfUpper : LfUpper := by
  intro y hy
  simp only [lf]
  have hn1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hny : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have h := log_factorial_le (n := ⌊y⌋₊) (by omega)
  have hn1' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn1
  have hg := g_mono hn1' hny
  have hl := Real.log_le_log (by linarith) hny
  linarith

theorem lfLower : LfLower := by
  intro y hy
  simp only [lf]
  have hn1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hn1' : (1 : ℝ) ≤ ⌊y⌋₊ := by exact_mod_cast hn1
  have hy' : y ≤ (⌊y⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one y).le
  have hS := Stirling.le_log_factorial_stirling (n := ⌊y⌋₊ + 1) (Nat.succ_ne_zero _)
  have hfac : Real.log (((⌊y⌋₊ + 1) ! : ℕ) : ℝ) =
      Real.log ((⌊y⌋₊ : ℝ) + 1) + Real.log ((⌊y⌋₊ ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    ring
  have h2π := log_two_pi_ge
  have hh := h_le hy hy' (by linarith)
  push_cast at hS hfac
  linarith

theorem main_term {x : ℝ} (hx : 0 < x) :
    (x * log x - x) - (x / 2 * log (x / 2) - x / 2) - (x / 3 * log (x / 3) - x / 3)
      - (x / 5 * log (x / 5) - x / 5) + (x / 30 * log (x / 30) - x / 30) = chA * x := by
  have h2 : log (x / 2) = log x - log 2 := Real.log_div hx.ne' (by norm_num)
  have h3 : log (x / 3) = log x - log 3 := Real.log_div hx.ne' (by norm_num)
  have h5 : log (x / 5) = log x - log 5 := Real.log_div hx.ne' (by norm_num)
  have h30 : log (x / 30) = log x - log 30 := Real.log_div hx.ne' (by norm_num)
  rw [h2, h3, h5, h30]
  simp only [chA]
  ring

theorem stir_log_thirty : log 30 = log 2 + log 3 + log 5 := by
  rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]

theorem dUpper : DUpper := by
  intro x hx
  simp only [chD]
  have hx0 : (0 : ℝ) < x := by linarith
  have l1 := lfUpper x (by linarith)
  have l30 := lfUpper (x / 30) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u2 := lfLower (x / 2) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u3 := lfLower (x / 3) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have u5 := lfLower (x / 5) (by rw [le_div_iff₀ (by norm_num)]; linarith)
  have hm := main_term hx0
  have h2 : log (x / 2) = log x - log 2 := Real.log_div hx0.ne' (by norm_num)
  have h3 : log (x / 3) = log x - log 3 := Real.log_div hx0.ne' (by norm_num)
  have h5 : log (x / 5) = log x - log 5 := Real.log_div hx0.ne' (by norm_num)
  have h30 : log (x / 30) = log x - log 30 := Real.log_div hx0.ne' (by norm_num)
  have hl30 := log_thirty_ge
  have hs := stir_log_thirty
  linarith

end PI.PC
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiUpperBoundOfLtThirtyMulSixPow

section

@[expose] public section

namespace PI.PC

open Real

theorem log_thirty : log 30 = log 2 + log 3 + log 5 := by
  rw [← log_mul (by norm_num) (by norm_num), ← log_mul (by norm_num) (by norm_num)]
  norm_num

theorem log_six : log 6 = log 2 + log 3 := by
  rw [← log_mul (by norm_num) (by norm_num)]
  norm_num

theorem chebyshevConstantNumeric : ANum := by
  have h2 := log_two_gt_d9
  have h2' := log_two_lt_d9
  have h3 := log_three_gt_d9
  have h3' := log_three_lt_d9
  have h5 := log_five_gt_d9
  have h5' := log_five_lt_d9
  unfold ANum chA
  rw [log_thirty]
  constructor <;> norm_num at * <;> linarith

theorem lcmUpto_le_three_pow : ∀ n < 30, Nat.lcmUpto n ≤ 3 ^ n := by
  decide +kernel

theorem psi_le_of_lt_thirty {x : ℝ} (h0 : 0 ≤ x) (hx : x < 30) : Chebyshev.psi x ≤ 1.1056 * x := by
  have hn : ⌊x⌋₊ < 30 := (Nat.floor_lt h0).2 (by exact_mod_cast hx)
  rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  have h1 : ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ (3 : ℝ) ^ ⌊x⌋₊ := by
    exact_mod_cast lcmUpto_le_three_pow _ hn
  have h2 : log ((Nat.lcmUpto ⌊x⌋₊ : ℕ) : ℝ) ≤ log ((3 : ℝ) ^ ⌊x⌋₊) :=
    log_le_log (by exact_mod_cast Nat.lcmUpto_pos _) h1
  rw [log_pow] at h2
  have h3 := log_three_lt_d9
  have h4 : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le h0
  have h5 : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have h6 : ((⌊x⌋₊ : ℕ) : ℝ) * log 3 ≤ ((⌊x⌋₊ : ℕ) : ℝ) * 1.1056 :=
    mul_le_mul_of_nonneg_left (by norm_num at h3 ⊢; linarith) h5
  nlinarith

theorem psiUpperBound_of_lt_thirty_mul_six_pow (hA : ANum) (hD : DUpper) (hS : Sandwich) (k : ℕ) :
    ∀ x : ℝ, 1 ≤ x → x < 30 * 6 ^ k → Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (log x) ^ 2 := by
  induction k with
  | zero =>
    intro x h1 hx
    have := psi_le_of_lt_thirty (by linarith) (by simpa using hx)
    have := sq_nonneg (log x)
    linarith
  | succ k ih =>
    intro x h1 hx
    rcases lt_or_ge x 30 with h30 | h30
    · have := psi_le_of_lt_thirty (by linarith) h30
      have := sq_nonneg (log x)
      linarith
    · have hx6 : x / 6 < 30 * 6 ^ k := by
        rw [div_lt_iff₀ (by norm_num)]
        calc x < 30 * 6 ^ (k + 1) := hx
          _ = 30 * 6 ^ k * 6 := by ring
      have e1 := ih (x / 6) (by linarith) hx6
      have e2 := (hS x (by linarith)).1
      have e3 := hD x h30
      have e4 : chA * x ≤ 0.9213 * x := mul_le_mul_of_nonneg_right hA.2 (by linarith)
      have hl : log (x / 6) = log x - log 6 := log_div (by linarith) (by norm_num)
      rw [hl] at e1
      have hL : 0 ≤ log x := log_nonneg h1
      have l6a : 1.7917 ≤ log 6 := by
        rw [log_six]; have := log_two_gt_d9; have := log_three_gt_d9; norm_num at *; linarith
      have l6b : log 6 ≤ 1.7918 := by
        rw [log_six]; have := log_two_lt_d9; have := log_three_lt_d9; norm_num at *; linarith
      have p1 : 0 ≤ (1.4 * log 6 - 2.5) * log x := mul_nonneg (by linarith) hL
      have p2 : (log 6) ^ 2 ≤ 1.7918 ^ 2 := pow_le_pow_left₀ (by linarith) l6b 2
      nlinarith

theorem chUpper_of (hA : ANum) (hD : DUpper) (hS : Sandwich) : CHUpper := by
  intro x h1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 6)
  refine psiUpperBound_of_lt_thirty_mul_six_pow hA hD hS k x h1 ?_
  have : (0 : ℝ) < 6 ^ k := by positivity
  linarith

end PI.PC
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.PsiLowerBoundHolds

section

@[expose] public section

namespace PI.PC

theorem psiUpperBound_holds : CHUpper := chUpper_of chebyshevConstantNumeric dUpper sandwich

end PI.PC
end
end
