module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
public import Development.AutomorphicArithmetic.MeanSquareBounds.SumMinLeDiv
public import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.Primorial

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagB

section

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem sum_log_sq_div_sq_primes_dyadic_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      2 * Real.log 4 * Real.log (2 * y) / y := by
  have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < y := by linarith
  have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
  have hL0 : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hy2pos : 0 < (y:ℝ) ^ 2 := by positivity
  have hterm : ∀ p ∈ (Ioc y (2 * y)).filter Nat.Prime,
      Real.log p ^ 2 / (p : ℝ) ^ 2 ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hpr⟩ := hp
    have hp1 : (y:ℝ) < p := by exact_mod_cast h1
    have hp2 : (p:ℝ) ≤ 2 * y := by exact_mod_cast h2
    have hppos : (0:ℝ) < p := by linarith
    have hp2pos : 0 < (p:ℝ) ^ 2 := by positivity
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have hlle : Real.log p ≤ Real.log (2 * y) := Real.log_le_log hppos hp2
    have hyp : (y:ℝ) ^ 2 ≤ (p:ℝ) ^ 2 := by nlinarith
    have hnum : 0 ≤ Real.log (2 * y) * Real.log p := mul_nonneg hL0 hlp
    calc Real.log p ^ 2 / (p:ℝ) ^ 2 = Real.log p * Real.log p / (p:ℝ) ^ 2 := by ring
      _ ≤ Real.log (2 * y) * Real.log p / (p:ℝ) ^ 2 := by
          gcongr ?_ * _ / _
      _ ≤ Real.log (2 * y) * Real.log p / (y:ℝ) ^ 2 := by
          gcongr _ / ?_
      _ = Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p := by ring
  have hsum : ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ≤ 2 * y * Real.log 4 := by
    have hsub : (Ioc y (2 * y)).filter Nat.Prime ⊆ (Finset.range (2 * y + 1)).filter Nat.Prime := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp.2⟩
    calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p
        ≤ ∑ p ∈ (Finset.range (2 * y + 1)).filter Nat.Prime, Real.log p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
      _ = Real.log (primorial (2 * y)) := by
          rw [primorial, Nat.cast_prod, Real.log_prod]
          intro p hp
          rw [Finset.mem_filter] at hp
          exact_mod_cast hp.2.ne_zero
      _ ≤ Real.log (4 ^ (2 * y)) := by
          apply Real.log_le_log
          · exact_mod_cast primorial_pos (2 * y)
          · exact_mod_cast primorial_le_four_pow (2 * y)
      _ = 2 * y * Real.log 4 := by
          rw [Real.log_pow]
          push_cast
          ring
  calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log (2 * y) / (y:ℝ) ^ 2 * Real.log p :=
        Finset.sum_le_sum hterm
    _ = Real.log (2 * y) / (y:ℝ) ^ 2 * ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p := by
        rw [Finset.mul_sum]
    _ ≤ Real.log (2 * y) / (y:ℝ) ^ 2 * (2 * y * Real.log 4) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hL0 (sq_nonneg _))
    _ = 2 * Real.log 4 * Real.log (2 * y) / y := by
        field_simp

theorem sum_log_sq_div_sq_primes_tail_le (N : ℕ) : ∀ d y : ℕ, 1 ≤ y → N - y ≤ d →
    ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 ≤
      4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
  intro d
  induction d with
  | zero =>
    intro y hy hd
    have hN : N ≤ y := by omega
    rw [Finset.Ioc_eq_empty_of_le hN, Finset.filter_empty, Finset.sum_empty]
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) h4) (by linarith)) (by positivity)
  | succ d ih =>
    intro y hy hd
    have hyR : (1:ℝ) ≤ y := by exact_mod_cast hy
    have hy0 : (0:ℝ) < y := by linarith
    have hy0' : (y:ℝ) ≠ 0 := ne_of_gt hy0
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hly : 0 ≤ Real.log y := Real.log_nonneg hyR
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2y : Real.log (2 * y) = Real.log 2 + Real.log y :=
      Real.log_mul (by norm_num) hy0'
    have hblock := sum_log_sq_div_sq_primes_dyadic_le y hy
    by_cases hN : N ≤ 2 * y
    · have hsub : (Ioc y N).filter Nat.Prime ⊆ (Ioc y (2 * y)).filter Nat.Prime :=
        Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hN)
      calc ∑ p ∈ (Ioc y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
        _ ≤ 2 * Real.log 4 * Real.log (2 * y) / y := hblock
        _ ≤ 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            gcongr ?_ / _
            rw [hlog2y]
            nlinarith [mul_nonneg hl4 hly, mul_nonneg hl4 hl2]
    · push_neg at hN
      have hsplit : (Ioc y N).filter Nat.Prime =
          (Ioc y (2 * y)).filter Nat.Prime ∪ (Ioc (2 * y) N).filter Nat.Prime := by
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (by omega) hN.le]
      have hdisj : Disjoint ((Ioc y (2 * y)).filter Nat.Prime) ((Ioc (2 * y) N).filter Nat.Prime) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_Ioc] at ha hb
        omega
      have ht := ih (2 * y) (by omega) (by omega)
      rw [hsplit, Finset.sum_union hdisj]
      calc ∑ p ∈ (Ioc y (2 * y)).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 +
            ∑ p ∈ (Ioc (2 * y) N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2
          ≤ 2 * Real.log 4 * Real.log (2 * y) / y +
            4 * Real.log 4 * (Real.log ((2 * y : ℕ) : ℝ) + 2 * Real.log 2) / ((2 * y : ℕ) : ℝ) :=
            add_le_add hblock ht
        _ = 4 * Real.log 4 * (Real.log y + 2 * Real.log 2) / y := by
            push_cast
            rw [hlog2y]
            field_simp <;> ring

theorem sP_cN_nonneg (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) : 0 ≤ sP (cN x) N p := by
  unfold sP cN
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

theorem sP_cN_le_log_div (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) (hp : p.Prime) :
    sP (cN x) N p ≤ 2 * x * Real.log p / p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp2
  have hppos : (0:ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  set r : ℝ := 1 / (p:ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hppos]; linarith
  have hrh : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hpR
  have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
      (Icc 1 N).image (fun k => p ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hpp, hmf⟩ := hn
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p = q := by
      have h1 : p ∣ q ^ k := by rw [← hmf]; exact Nat.minFac_dvd _
      exact (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h1)
    subst hpq
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Icc.mpr ⟨hk, ?_⟩, rfl⟩
    have hlt := Nat.lt_pow_self (by omega : 1 < p) (n := k)
    exact le_of_lt (lt_of_lt_of_le hlt hnN)
  have h1 : sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
      Real.log p * (x / n) := by
    unfold sP
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_filter] at hn
    unfold cN
    rw [ArithmeticFunction.vonMangoldt_apply, if_pos hn.2.1, hn.2.2]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hlog
  calc sP (cN x) N p ≤ ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
        Real.log p * (x / n) := h1
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * (x / n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun n _ _ => mul_nonneg hlog (div_nonneg hx (Nat.cast_nonneg n)))
    _ = ∑ k ∈ Icc 1 N, Real.log p * x * r ^ k := by
        rw [Finset.sum_image (Nat.pow_right_injective hp2).injOn]
        apply Finset.sum_congr rfl
        intro k _
        show Real.log p * (x / ((p ^ k : ℕ) : ℝ)) = Real.log p * x * r ^ k
        rw [hr, Nat.cast_pow, one_div, inv_pow]
        ring
    _ ≤ ∑ k ∈ Ico 1 (N + 1), Real.log p * x * r ^ k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          rw [Finset.mem_Icc] at hk
          rw [Finset.mem_Ico]
          omega
        · intro k _ _
          exact mul_nonneg (mul_nonneg hlog hx) (pow_nonneg hr0 k)
    _ = Real.log p * x * ∑ k ∈ Ico 1 (N + 1), r ^ k := by rw [Finset.mul_sum]
    _ ≤ Real.log p * x * (r ^ 1 / (1 - r)) :=
        mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (mul_nonneg hlog hx)
    _ ≤ Real.log p * x * (2 * r) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlog hx)
        rw [pow_one, div_le_iff₀ (by linarith)]
        nlinarith
    _ = 2 * x * Real.log p / p := by rw [hr]; ring

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end
end

-- Source module: Development.AutomorphicArithmetic.MeanSquareBounds.SPsqLe

section

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem sum_log_primes_le_mul_log_four (Y : ℕ) :
    ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ Y * Real.log 4 := by
  rw [← Real.log_prod]
  · have h1 : ((primorial Y : ℕ) : ℝ) ≤ (4 : ℝ) ^ Y := by exact_mod_cast primorial_le_four_pow Y
    have h2 : ((primorial Y : ℕ) : ℝ) = ∏ p ∈ (range (Y + 1)).filter Nat.Prime, (p : ℝ) := by
      simp [primorial, Nat.cast_prod]
    rw [← h2, ← Real.log_pow]
    have hpos : (0 : ℝ) < (primorial Y : ℕ) := by exact_mod_cast primorial_pos Y
    exact Real.log_le_log hpos h1
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

private theorem sum_sP_sq_large_primes_le (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ 96 * Real.log 4 * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  have hY3 : 3 ≤ Y := Nat.le_floor (by exact_mod_cast hy)
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hYlt : y < (Y : ℝ) + 1 := Nat.lt_floor_add_one y
  have hY3r : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hy0 : 0 < y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hset : ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ Y) = (Ioc Y N).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨by omega, h2⟩, hp⟩, by omega⟩
  rw [hset]
  have hterm : ∀ p ∈ (Ioc Y N).filter Nat.Prime,
      sP (cN y) N p ^ 2 ≤ 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := sP_cN_le_log_div y hy0.le N p hpp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    calc sP (cN y) N p ^ 2 ≤ (2 * y * Real.log p / p) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
        field_simp
        ring
  have htail := sum_log_sq_div_sq_primes_tail_le N (N - Y) Y (by omega) le_rfl
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogY : Real.log Y ≤ Real.log y := Real.log_le_log hY0 hYle
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
  have hq : 4 * Real.log 4 * (Real.log Y + 2 * Real.log 2) / Y ≤ 24 * Real.log 4 * Real.log y / y := by
    rw [div_le_div_iff₀ hY0 hy0]
    have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hE : Real.log Y + 2 * Real.log 2 ≤ 3 * Real.log y := by linarith
    have h1 : (Real.log Y + 2 * Real.log 2) * y ≤ 3 * Real.log y * y :=
      mul_le_mul_of_nonneg_right hE hy0.le
    have h2 : 3 * Real.log y * y ≤ 3 * Real.log y * (2 * Y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 4 * Real.log 4 by positivity)
    nlinarith
  calc ∑ p ∈ (Ioc Y N).filter Nat.Prime, sP (cN y) N p ^ 2
      ≤ ∑ p ∈ (Ioc Y N).filter Nat.Prime, 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := sum_le_sum hterm
    _ = 4 * y ^ 2 * ∑ p ∈ (Ioc Y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 4 * y ^ 2 * (24 * Real.log 4 * Real.log y / y) := by
        gcongr
        exact htail.trans hq
    _ = 96 * Real.log 4 * (y * Real.log y) := by
        field_simp
        ring

private theorem sum_sP_sq_small_primes_le_of_bound (C0 : ℝ) (hC0 : 0 < C0)
    (hb : ∀ (y : ℝ), 3 ≤ y → ∀ (N p : ℕ), sP (cN y) N p ≤ C0 * Real.log y) (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ (4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4) * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  set S := ⌊Real.sqrt y⌋₊ with hSdef
  have hy0 : 0 < y := by linarith
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hsq0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hSle : (S : ℝ) ≤ Real.sqrt y := Nat.floor_le hsq0
  have hSlt : Real.sqrt y < (S : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsqsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hsq1 : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogsq : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0.le
  have hlsy : Real.log y ≤ 2 * Real.sqrt y := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt y by linarith)
    rw [hlogsq] at this
    linarith
  have hsub : ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ Y) ⊆ (range (Y + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
    exact ⟨by omega, hp.1.2⟩
  have step1 := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => sP (cN y) N p ^ 2) (fun p _ _ => sq_nonneg _)
  have hterm : ∀ p ∈ (range (Y + 1)).filter Nat.Prime, sP (cN y) N p ^ 2 ≤
      (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0) + 2 * C0 ^ 2 * Real.log y * Real.log p := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := hb y hy N p
    have hsqb : sP (cN y) N p ^ 2 ≤ C0 ^ 2 * Real.log y ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ h0 h1 2
    have hx : 0 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by positivity
    split_ifs with hpS
    · linarith
    · have hpS' : (S : ℝ) + 1 ≤ p := by exact_mod_cast (show S + 1 ≤ p by omega)
      have hlt : Real.sqrt y < p := by linarith
      have hlog : Real.log (Real.sqrt y) ≤ Real.log p := Real.log_le_log (by linarith) hlt.le
      rw [hlogsq] at hlog
      have : C0 ^ 2 * Real.log y ^ 2 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by
        have hc : 0 ≤ C0 ^ 2 * Real.log y := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (show Real.log y ≤ 2 * Real.log p by linarith) hc]
      linarith
  have step2 := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at step2
  have hite : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0)
      ≤ ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
    rw [← sum_filter]
    have hsub2 : ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S) ⊆ range (S + 1) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp ⊢
      omega
    calc ∑ p ∈ ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S), C0 ^ 2 * Real.log y ^ 2
        ≤ ∑ p ∈ range (S + 1), C0 ^ 2 * Real.log y ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => by positivity)
      _ = ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  have htheta := sum_log_primes_le_mul_log_four Y
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hA : ((S : ℝ) + 1) * Real.log y ≤ 4 * y := by
    have : ((S : ℝ) + 1) * Real.log y ≤ (Real.sqrt y + 1) * (2 * Real.sqrt y) :=
      mul_le_mul (by linarith) hlsy hly (by linarith)
    nlinarith
  have hA' : ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) ≤ 4 * C0 ^ 2 * (y * Real.log y) := by
    have := mul_le_mul_of_nonneg_right hA (show 0 ≤ C0 ^ 2 * Real.log y by positivity)
    nlinarith
  have hB : 2 * C0 ^ 2 * Real.log y * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p
      ≤ 2 * C0 ^ 2 * Real.log 4 * (y * Real.log y) := by
    have h1 : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ y * Real.log 4 :=
      htheta.trans (mul_le_mul_of_nonneg_right hYle hL.le)
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C0 ^ 2 * Real.log y by positivity)
    nlinarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := by linarith

theorem sPsq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N : ℕ,
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN y) N p ^ 2 ≤ C * y * Real.log y := by
  obtain ⟨C0, hC0, hb⟩ := exists_primePowerSum_le_mul_log
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4 + 96 * Real.log 4, by positivity, ?_⟩
  intro y hy N
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => p ≤ ⌊y⌋₊)]
  have h3 := sum_sP_sq_small_primes_le_of_bound C0 hC0 hb y hy N
  have h2 := sum_sP_sq_large_primes_le y hy N
  nlinarith

end QH
end
end
