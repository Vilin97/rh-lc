module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensBlock
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDetect
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll
import Formalism.LFunctionBounds.LFunctionBoundsProofs.LPartialSum
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DyadicSizeLePowTwelveSecond

section

@[expose] public section

open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem log_pow_five_le_sqrt (c : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 5 ≤ Real.sqrt q := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 10)).bound
    (c := 1 / (c ^ 2 + 1)) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 h
  refine ⟨⌈x₀⌉₊, fun q hq => ?_⟩
  have hqx : x₀ ≤ (q : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hq)
  have h1 := hx₀ q hqx
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hq0] at h1
  have h2 : Real.log q ^ 10 ≤ 1 / (c ^ 2 + 1) * q := (le_abs_self _).trans h1
  have h3 : (c ^ 2 + 1) * Real.log q ^ 10 ≤ q := by
    have hp : (0 : ℝ) < c ^ 2 + 1 := by positivity
    calc (c ^ 2 + 1) * Real.log q ^ 10 ≤ (c ^ 2 + 1) * (1 / (c ^ 2 + 1) * q) := by gcongr
      _ = (q : ℝ) := by field_simp
  have h4 : (c * Real.log q ^ 5) ^ 2 ≤ q := by
    have : (0 : ℝ) ≤ Real.log q ^ 10 := by positivity
    nlinarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h4)

theorem one_le_log_of_three_le_second {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem dyadic_index_le_log_second (q : ℕ) (hq : 3 ≤ q) : ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) ≤ 24 * Real.log q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 q ≤ q := by exact_mod_cast h1
  have h3 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2
  have h4 := Real.log_two_gt_d9
  have h5 := one_le_log_of_three_le_second hq'
  have h6 : (0 : ℝ) ≤ (Nat.log 2 q : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem dyadic_size_le_pow_twelve_second (q : ℕ) (hq : 256 ≤ q) : q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1)) ≤ q ^ 12 := by
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ (8 * (Nat.log 2 q + 1)) = 256 * (2 ^ Nat.log 2 q) ^ 8 := by
    rw [← pow_mul]; rw [show 8 * (Nat.log 2 q + 1) = 8 + Nat.log 2 q * 8 by ring, pow_add]; norm_num
  rw [h2]
  calc q ^ 3 * (256 * (2 ^ Nat.log 2 q) ^ 8) ≤ q ^ 3 * (q * q ^ 8) := by gcongr
    _ = q ^ 12 := by ring

theorem second_small_condition (u l K J q s Lq : ℝ) (hq : 0 < q) (hs : 0 < s) (hu : u ≤ 1 / (q * s))
    (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 48 * q) (hJ0 : 0 < J) (hJ : J ≤ 24 * Lq)
    (hc : 971882496 * Lq ^ 5 ≤ s) : 2 * u * l ^ 3 * K ≤ (1 / (2 * J)) ^ 2 / 2 := by
  have hL : 0 < Lq := by nlinarith
  have h1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by
    have : 0 ≤ 1 / (q * s) := by positivity
    calc 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by gcongr
      _ ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by gcongr
  have h2 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) = 210912 * Lq ^ 3 / s := by
    field_simp; ring
  have h3 : 1 / (4608 * Lq ^ 2) ≤ (1 / (2 * J)) ^ 2 / 2 := by
    have : (1 / (2 * J)) ^ 2 / 2 = 1 / (8 * J ^ 2) := by field_simp; ring
    rw [this]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h4 : 210912 * Lq ^ 3 / s ≤ 1 / (4608 * Lq ^ 2) := by
    rw [div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith

theorem rpow_neg_exponent_bound_second (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq'
  have hU' : (q : ℝ) ^ 3 ≤ U := by exact_mod_cast hU
  have h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)
  have h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  linarith

theorem rpow_pos_exponent_bound_second (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have hU' : (U : ℝ) ≤ (2 * x) ^ 12 := by
    calc (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
      _ ≤ (2 * x) ^ 12 := by gcongr
  have h1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hU' (by linarith)
  have h2 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 * x) ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have h3 : (2 * x) ^ (24 * (1 - σ)) = 2 ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) :=
    Real.mul_rpow (by norm_num) hx.le
  have h4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    have : (2 : ℝ) ^ (6 : ℝ) = 64 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h5 : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  rw [h2, h3] at h1
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ZeroDetectionSecond

section

@[expose] public section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

attribute [local irreducible] qd pYd pJd pNd in
theorem zero_detection_second : Detect1 := by
  intro M _ χ hχ1 T hT hM ρ hρ hρim hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, qd M T = X := ⟨_, rfl⟩
  have hMT : (M : ℝ) * T ≤ X := by rw [← hX]; unfold qd; exact Nat.le_ceil _
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX6 : (6 : ℝ) ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hre0 : 0 < ρ.re := by linarith
  have hNX : X ^ 8 ≤ pNd M T := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pNd pJd
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pYd M T = X ^ 3 := by unfold pYd; rw [hX]
  have hYN : pYd M T ≤ pNd M T := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pYd M T := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pNd M T := le_trans hY1 hYN
  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum M χ hχ1 _ hB ρ hre0 (pNd M T) hN1
  rw [hL, zero_sub, norm_neg] at hP
  have hMI := mollifier_identity M χ ρ (pYd M T) (pNd M T) (pYd M T * pNd M T) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pYd M T)
  set P := ∑ n ∈ Icc 1 (pNd M T), χ (n : ZMod M) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) * χ (d : ZMod M) * (d : ℂ) ^ (-ρ)
    with hMdef
  set D := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n * χ (n : ZMod M) * (n : ℂ) ^ (-ρ)
    with hD
  have hnum : ‖P‖ * (pYd M T : ℝ) ≤ 1 / 2 := by
    have hXpos : (0 : ℝ) < X := by linarith
    have hNpos : (0 : ℝ) < pNd M T := by exact_mod_cast hN1
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T := by
      have h1 : ‖ρ‖ ≤ ρ.re + T := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re := by
        rw [div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : T / ρ.re ≤ 4 / 3 * T := by
        rw [div_le_iff₀ hre0]; nlinarith
      linarith
    have hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ) := by exact_mod_cast hNX
    have hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]
        norm_num
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ) := by rw [hY, Nat.cast_pow]
    have hc : 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 8 * X := by
      have hpos : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * ((M : ℝ) + 1) * (3 * T) :=
            mul_le_mul_of_nonneg_left hrho (by positivity)
        _ ≤ 8 * X := by nlinarith
    have hPle : ‖P‖ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := by
      refine hP.trans ?_
      have a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := hpow.trans hinv
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 8 * X * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (3 : ℕ) ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) * (X : ℝ) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 8 / X ^ 2 := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI, norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pYd M T : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have hsplit : D = ∑ j ∈ range (pJd M T),
      blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ := by
    rw [hD, show pNd M T = 2 ^ pJd M T by unfold pNd; rfl, sum_blocks]
    rfl
  by_contra hcon
  push Not at hcon
  have hJ8 : 8 ≤ pJd M T := by unfold pJd; omega
  have hJpos : (0 : ℝ) < pJd M T := by exact_mod_cast (by omega : 0 < pJd M T)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJd M T)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJd M T), ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ‖
        < ∑ j ∈ range (pJd M T), 1 / (2 * (pJd M T : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.SecondBlockCount

section

@[expose] public section

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem second_block_count (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)) (U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 256 ≤ qd M T)
    (hc : 971882496 * Real.log (qd M T) ^ 5 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) U (fun n => p.1 (n : ZMod M)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) := by
  set q := qd M T with hqdef
  set x : ℝ := (M : ℝ) * T with hx
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ x := by rw [hx]; nlinarith
  have hxq : x ≤ q := Nat.le_ceil x
  have hqx1 : (q : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqx : (q : ℝ) ≤ 2 * x := by linarith
  have hq' : (256 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le_second (by linarith)
  have hLq1 : 1 ≤ Real.log q := one_le_log_of_three_le_second (by linarith)
  have hLq : Real.log q ≤ 2 * Real.log x := by
    have h1 : Real.log q ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hU : 1 ≤ U := le_trans (Nat.one_le_pow _ _ (by omega)) hU1
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log q := dyadic_index_le_log_second q (by omega)
  have hJ0 : (0 : ℝ) < (pJd M T : ℝ) := by
    have : 0 < pJd M T := by unfold pJd; omega
    exact_mod_cast this
  have hl0 : 0 ≤ Real.log (2 * (U : ℝ)) := Real.log_nonneg (by linarith)
  have hl : 1 + Real.log (2 * (U : ℝ)) ≤ 13 * Real.log q := by
    have h1 : (2 * (U : ℝ)) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU2
    have h2 : Real.log (2 * (U : ℝ)) ≤ Real.log ((q : ℝ) ^ 12) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hG : 9 + 8 * Real.log (2 * T + 1) ≤ 17 * Real.log x := by
    have h1 : Real.log (2 * T + 1) ≤ Real.log x :=
      Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
    linarith
  have hG0 : 0 ≤ 9 + 8 * Real.log (2 * T + 1) := by
    have : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
    linarith
  have hK0 : 0 ≤ 8 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hK : 8 * ((M : ℝ) + 1) * (2 + 2 * T) ≤ 48 * q := by
    have : 8 * ((M : ℝ) + 1) * (2 + 2 * T) ≤ 48 * x := by rw [hx]; nlinarith
    linarith
  have hθ : (0 : ℝ) < 1 / (2 * (pJd M T : ℝ)) := by positivity
  have hsmall := second_small_condition ((U : ℝ) ^ (1 - 2 * σ)) (1 + Real.log (2 * (U : ℝ)))
    (8 * ((M : ℝ) + 1) * (2 + 2 * T)) (pJd M T : ℝ) q (Real.sqrt q) (Real.log q) (by linarith)
    (Real.sqrt_pos.2 (by linarith)) (rpow_neg_exponent_bound_second q U σ (by omega) hσ hU1) (by linarith) hl hK0 hK
    hJ0 hJ hc
  have hmain := dyadic_block_count S (fun p n => p.1 (n : ZMod M)) (fun p => p.2) (pYd M T) (pNd M T) U σ
    (1 / (2 * (pJd M T : ℝ))) (9 + 8 * Real.log (2 * T + 1)) (8 * ((M : ℝ) + 1) * (2 + 2 * T))
    hU hθ (by linarith) hG0 hK0 (fun p _ n => DirichletCharacter.norm_le_one _ _)
    (fun p hp => (hS p hp).1)
    (off_diagonal_bound M S σ T U hU hT (by linarith) hS hsp) hbig hsmall
  refine hmain.trans ?_
  have hu2 := rpow_pos_exponent_bound_second q U x σ (by linarith) hqx hσ hσ1 (by omega)
  have hu0 : 0 ≤ (U : ℝ) ^ (2 - 2 * σ) := by positivity
  have he : 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) / (1 / (2 * (pJd M T : ℝ))) ^ 2 =
      4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) * (4 * (pJd M T : ℝ) ^ 2) := by
    field_simp
    ring
  rw [he]
  have hl' : 1 + Real.log (2 * (U : ℝ)) ≤ 26 * Real.log x := by linarith
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log x := by linarith
  have hl00 : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by linarith
  gcongr

theorem zero_count_second : Count1 := by
  obtain ⟨q₁, hq₁⟩ := log_pow_five_le_sqrt 971882496
  refine ⟨48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)), max q₁ 256, ?_⟩
  intro M _ T σ S hM hT hσ hq hS hsp
  have hq256 : 256 ≤ qd M T := le_trans (le_max_right _ _) hq
  have hc := hq₁ (qd M T) (le_trans (le_max_left _ _) hq)
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ (M : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ Real.log ((M : ℝ) * T) := one_le_log_of_three_le_second (by linarith)
  have hX0 : 0 ≤ ((M : ℝ) * T) ^ (24 * (1 - σ)) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [card_empty, Nat.cast_zero]; positivity
  have hσ1 : σ ≤ 1 := by
    obtain ⟨-, h1, h2, -⟩ := hS p₀ hp₀
    linarith
  set B : ℝ := 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  classical
  let Sj : ℕ → Finset (DirichletCharacter ℂ M × ℂ) := fun j =>
    S.filter (fun p => 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => p.1 (n : ZMod M)) p.2‖)
  have hsub : S ⊆ (range (pJd M T)).biUnion Sj := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
    obtain ⟨j, hj, hjb⟩ := zero_detection_second M p.1 h1 T hT hM p.2 (by linarith) h4 h5
    exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hp, hjb⟩⟩
  have hj : ∀ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ B := by
    intro j hj
    have hjJ : j < pJd M T := mem_range.1 hj
    have hYN : qd M T ^ 3 * 2 ^ pJd M T ≤ qd M T ^ 12 := dyadic_size_le_pow_twelve_second (qd M T) hq256
    apply second_block_count M T σ (Sj j) (pYd M T * 2 ^ j) hM hT hσ hσ1 hq256 hc
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc 2 * (pYd M T * 2 ^ j) = qd M T ^ 3 * 2 ^ (j + 1) := by unfold pYd; ring
        _ ≤ qd M T ^ 3 * 2 ^ pJd M T := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := hYN
    · intro p hp
      obtain ⟨-, h2, h3, h4, -⟩ := hS p (mem_filter.1 hp).1
      exact ⟨h2, h3.le, h4⟩
    · intro p hp p' hp'
      exact hsp p (mem_filter.1 hp).1 p' (mem_filter.1 hp').1
    · intro p hp
      exact (mem_filter.1 hp).2
  have h1 : (S.card : ℝ) ≤ ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  have h2 : ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ (pJd M T : ℝ) * B := by
    have := sum_le_card_nsmul (range (pJd M T)) (fun j => ((Sj j).card : ℝ)) B hj
    simpa using this
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) := by
    have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log (qd M T) := dyadic_index_le_log_second (qd M T) (by omega)
    have hqx1 : ((qd M T : ℕ) : ℝ) < (M : ℝ) * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hq' : (256 : ℝ) ≤ (qd M T : ℝ) := by exact_mod_cast hq256
    have h3 : Real.log (qd M T) ≤ Real.log (2 * ((M : ℝ) * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have h4 : Real.log 2 ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : (pJd M T : ℝ) * B ≤ 48 * Real.log ((M : ℝ) * T) * B := by gcongr
  have h4 : 48 * Real.log ((M : ℝ) * T) * B =
      48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)) * ((M : ℝ) * T) ^ (24 * (1 - σ)) *
        Real.log ((M : ℝ) * T) ^ 7 := by
    rw [hB]; ring
  have h5 : Real.log ((M : ℝ) * T) ^ 7 ≤ Real.log ((M : ℝ) * T) ^ 10 :=
    pow_le_pow_right₀ hl1 (by norm_num)
  calc (S.card : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) * B := h1.trans (h2.trans h3)
    _ = _ := h4
    _ ≤ _ := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end
end
