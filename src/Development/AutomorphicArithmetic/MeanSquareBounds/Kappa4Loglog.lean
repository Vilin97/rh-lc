module

public import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.NumberTheory.Chebyshev
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
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContour
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailDiff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailNum
import Mathlib.NumberTheory.Chebyshev
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

-- Source module: Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mertensUpper

section

@[expose] public section

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem mertens_upper_sum_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ N * Real.log N - N + 1 + Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : Real.log ((N : ℝ) / (N + 1)) ≤ (N : ℝ) / (N + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hN'.ne' (by positivity)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ N + 1 by positivity)
    have h3 : ((N : ℝ) + 1) * ((N : ℝ) / (N + 1) - 1) = -1 := by field_simp; ring
    rw [h3] at h2
    push_cast
    nlinarith

theorem mertens_upper_log_le (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / c by positivity)
  rw [Real.log_div hx.ne' hc.ne'] at h
  linarith

theorem mertens_upper_psi_bound (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n + 1 + Real.log N ≤ 3 * N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  by_cases h25 : 25 ≤ N
  · have hp := Chebyshev.psi_le hN'
    rw [Chebyshev.psi, Nat.floor_natCast] at hp
    have h25' : (25 : ℝ) ≤ N := by exact_mod_cast h25
    have hs : 5 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by linarith)
    have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
    have hL : Real.log N = 2 * Real.log (Real.sqrt N) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have hl := mertens_upper_log_le (Real.sqrt N) 4 (by linarith) (by norm_num)
    set s := Real.sqrt N
    have hl' : Real.log N ≤ 0.78 + s / 2 := by linarith
    have h5 : 2 * s * Real.log N ≤ 2 * s * (0.78 + s / 2) :=
      mul_le_mul_of_nonneg_left hl' (by linarith)
    have h6 : Real.log 4 * N ≤ 1.39 * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  · have h1 : ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n
        ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log n :=
      Finset.sum_le_sum fun n _ => ArithmeticFunction.vonMangoldt_le_log
    have h2 := mertens_upper_sum_log N hN
    have h24 : (N : ℝ) ≤ 24 := by exact_mod_cast (by omega : N ≤ 24)
    by_cases h3 : 3 ≤ N
    · have h3' : (3 : ℝ) ≤ N := by exact_mod_cast h3
      have hl := mertens_upper_log_le N 16 (by linarith) (by norm_num)
      have hl' : Real.log N ≤ 1.78 + N / 16 := by linarith
      have h5 : ((N : ℝ) + 2) * Real.log N ≤ (N + 2) * (1.78 + N / 16) :=
        mul_le_mul_of_nonneg_left hl' (by linarith)
      nlinarith
    · have h2' : (N : ℝ) ≤ 2 := by exact_mod_cast (by omega : N ≤ 2)
      have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
      have h5 : ((N : ℝ) + 2) * Real.log N ≤ (N + 2) * (N - 1) :=
        mul_le_mul_of_nonneg_left hl (by linarith)
      nlinarith

theorem mertens_upper_nat (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ Real.log N + 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hid := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at hid
  simp only [ArithmeticFunction.log_apply] at hid
  have h1 := mertens_upper_sum_log N hN
  have h2 := mertens_upper_psi_bound N hN
  have h3 : N * ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ) +
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have : N ≤ (N / n + 1) * n := by
        have := Nat.lt_div_mul_add (a := N) hn0
        nlinarith
      exact_mod_cast this
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    calc (N : ℝ) * (ArithmeticFunction.vonMangoldt n / n)
        = ArithmeticFunction.vonMangoldt n * ((N : ℝ) / n) := by ring
      _ ≤ ArithmeticFunction.vonMangoldt n * (((N / n : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hlt hΛ
      _ = _ := by ring
  rw [← hid] at h3
  refine le_of_mul_le_mul_left ?_ hN'
  nlinarith

theorem mertens_upper (y : ℝ) (hy : 1 ≤ y) :
    ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ Real.log y + 2 := by
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have h := mertens_upper_nat ⌊y⌋₊ hN
  have hN' : (0 : ℝ) < (⌊y⌋₊ : ℕ) := by exact_mod_cast hN
  have hl : Real.log (⌊y⌋₊ : ℕ) ≤ Real.log y :=
    Real.log_le_log hN' (Nat.floor_le (by linarith))
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp only [Nat.cast_zero, div_zero, zero_add]
  linarith

end Deduction

end
end
end

-- Source module: Development.AutomorphicArithmetic.MeanSquareBounds.Kappa4Loglog

section

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem kappa4_num (K : ℝ) (hK : 0 ≤ K) (s Q : ℝ) (hs : 3 ≤ s) (hQ : 0 < Q)
    (hQs : (s ^ 4) ^ 1006 ≤ Q) (x : ℝ) (hx : x = s ^ 10) :
    ((K * s ^ 4 * (s ^ 4 * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ 2 * K + 802 := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs.trans (le_self_pow₀ hs1 (by norm_num))
  have hx0 : 0 < x := by linarith
  have hxa : x ^ ((2 / 5) / 4 : ℝ) = s := by
    rw [hx, ← Real.rpow_natCast s 10, ← Real.rpow_mul hs0.le]
    norm_num
  apply le_of_mul_le_mul_left _ hx0
  rw [Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (2 / 5) hx0, hxa,
    Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q K _ _ _ hx0 hQ]
  have t3 := Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3
  have t1 : (s ^ 4) ^ 2 * s ≤ x := by
    rw [hx]
    calc (s ^ 4) ^ 2 * s = s ^ 9 := by ring
      _ ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
  have t2 : s ^ 4 * x ^ 403 / Q ≤ x := by
    rw [div_le_iff₀ hQ]
    have e : s ^ 4 * x ^ 403 = x * (s ^ 4) ^ 1006 := by
      rw [hx, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    rw [e]
    exact mul_le_mul_of_nonneg_left hQs hx0.le
  have u1 := mul_le_mul_of_nonneg_left t1 hK
  have u2 := mul_le_mul_of_nonneg_left t2 hK
  have u3 : (802 : ℝ) ≤ x * 802 := by linarith
  have e1 : K * (s ^ 4) ^ 2 * s = K * ((s ^ 4) ^ 2 * s) := mul_assoc _ _ _
  have e2 : x * (2 * K + 802) = K * x + K * x + x * 802 := by ring
  rw [e1, e2]
  exact add_le_add (add_le_add u1 u2) (t3.trans u3)

set_option maxRecDepth 4096 in
private theorem kappa4_loglog : ∃ C l₀ : ℝ, 1 ≤ l₀ ∧ ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    l₀ ≤ Real.log Q → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 1000 * Real.log (Real.log Q) + C := by
  obtain ⟨K, hK0, hK⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_contour ((2 / 5) / 1600) (by positivity) (by norm_num)
  have hev : ∀ᶠ l : ℝ in Filter.atTop, l ^ 1006 ≤ Real.exp l := by
    have h := (Real.tendsto_exp_div_pow_atTop 1006).eventually_ge_atTop 1
    filter_upwards [h, Filter.eventually_gt_atTop 0] with l hl hl0
    rwa [le_div_iff₀ (by positivity), one_mul] at hl
  obtain ⟨l₀, hl₀⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_ge_atTop 81))
  refine ⟨2 * K + 802 + 2, l₀, by linarith [(hl₀ l₀ le_rfl).2], ?_⟩
  intro Q N _ χ hQlo hgood
  obtain ⟨hχ, hNQ, hbox⟩ := hgood
  obtain ⟨hexp, h81⟩ := hl₀ _ hQlo
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  rw [Real.exp_log hQ0] at hexp
  have hQ2 : 2 ≤ Q := by
    have := Real.log_le_self hQ0.le
    linarith
  obtain ⟨s, hs0, hs4⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 4 = Real.log Q :=
    ⟨Real.log Q ^ ((4 : ℕ) : ℝ)⁻¹, Real.rpow_nonneg (by linarith) _,
      Real.rpow_inv_natCast_pow (by linarith) (by norm_num)⟩
  have hs3 : 3 ≤ s := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hs0
    rw [hs4]; linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = s ^ 10 := ⟨_, rfl⟩
  have hnum := kappa4_num K hK0 s Q hs3 hQ0 (by rw [hs4]; exact hexp) x hx
  rw [hs4] at hnum
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs3.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hx0 : 0 < x := by linarith
  have hlogz : Real.log (x ^ 400) = 1000 * Real.log (Real.log Q) := by
    rw [← hs4, hx, Real.log_pow, Real.log_pow, Real.log_pow]; push_cast; ring
  set z : ℝ := x ^ 400 with hz
  set η : ℝ := 1 / x ^ 2 with hη
  have hz1 : 1 ≤ z := one_le_pow₀ (by linarith)
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  have hzη : 0 < z * η := by positivity
  have hC := hK N χ Q z η hχ hQ2 hNQ hbox hz1 hη0 hη1
  have hD := Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ z (z * η) hz1 hzη
  set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP
  have hkey : ((z * η : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.negLD χ 1 - P) =
      -(Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) +
      (Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * P) := by ring
  have hnorm : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤
      (K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + z ^ 2 / Q)
        + z * η * (z * η + 1) * Real.log (z + z * η) / z) / (z * η) := by
    rw [le_div_iff₀ hzη]
    have h1 := congrArg norm hkey
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hzη.le] at h1
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ * (z * η) = z * η * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := mul_comm _ _
      _ = _ := h1
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        exact add_le_add hC hD
  have htail := hnorm.trans hnum
  have hPle : ‖P‖ ≤ Real.log z + 2 := by
    have hM : ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤ Real.log z + 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (Deduction.mertens_upper z hz1)
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
      · intro n _ _
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    refine le_trans (norm_sum_le _ _) (le_trans ?_ hM)
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχn : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    gcongr
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ (n : ZMod N)‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 := by gcongr
      _ = ArithmeticFunction.vonMangoldt n := mul_one _
  have hLD : logDerivLAtOne χ = -(Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, neg_neg]
  rw [hLD, norm_neg]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1‖ = ‖P + (Formalism.ZeroFreeDirichlet.negLD χ 1 - P)‖ := by rw [add_sub_cancel]
    _ ≤ ‖P‖ + ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := norm_add_le _ _
    _ ≤ _ := by rw [← hlogz]; linarith

theorem kappa4 :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 52 → 0 < A → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ A * Y ^ (ε / 5) * Real.log Y ^ 2 → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 4 * Real.log Y := by
  intro ε A hε hε1 hA
  obtain ⟨C, l₀, hl₀, hC⟩ := kappa4_loglog
  have e1 : ∀ᶠ Y : ℝ in Filter.atTop, l₀ ≤ Y ^ (ε / 6) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 6)).eventually_ge_atTop _
  have e2 : ∀ᶠ u : ℝ in Filter.atTop, ‖Real.log u‖ ≤ (1 / 26000) * ‖u‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num)
  have e3 : ∀ᶠ u : ℝ in Filter.atTop, 13 * (1000 * Real.log A + C) ≤ u := Filter.eventually_ge_atTop _
  have e4 := Real.tendsto_log_atTop.eventually (e2.and (e3.and (Filter.eventually_ge_atTop 1)))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 (e1.and (e4.and (Filter.eventually_gt_atTop 0)))
  refine ⟨Y₀, ?_⟩
  intro Y hY Q N _ χ hlo hhi hgood
  obtain ⟨h1, ⟨h2, h3, h4⟩, hY0⟩ := hY₀ Y hY
  have hb := hC Q N χ (h1.trans hlo) hgood
  have hu0 : 0 < Real.log Y := by linarith
  have hp : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  have hl : Real.log (Real.log Q) ≤ Real.log A + ε / 5 * Real.log Y + 2 * Real.log (Real.log Y) := by
    refine (Real.log_le_log (by linarith) hhi).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hA.ne' hp.ne', Real.log_rpow hY0,
      Real.log_pow]
    push_cast; ring
  rw [Real.norm_of_nonneg hu0.le, Real.norm_of_nonneg (Real.log_nonneg h4)] at h2
  have h5 : ε * Real.log Y ≤ 1 / 52 * Real.log Y := mul_le_mul_of_nonneg_right hε1.le hu0.le
  have h6 : ε / 5 * Real.log Y = ε * Real.log Y / 5 := by ring
  rw [h6] at hl
  linarith

end QH
end
end
