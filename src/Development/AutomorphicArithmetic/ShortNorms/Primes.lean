module

public import Development.AutomorphicArithmetic.ShortNorms.ShortNorm
public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Mathlib.NumberTheory.Chebyshev
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLFamRayStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrivialClassShortIntervalStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeErrorStatement
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesAPIntervalOfPrimesRel
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBound

section

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem sum_lam_zero_le_card_normPrimes (𝓕 : LFam) (d M : ℕ)
    (hN : ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p) (X Y : ℝ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, 𝓕.lam 0 n ≤
      2 * Real.log Y * ((GlobalTheory.Mem.An.normPrimes d M X Y).card : ℝ) +
        2 * (Chebyshev.psi Y - Chebyshev.theta Y) := by
  have hl : ∀ n, 𝓕.lam 0 n ≤ 2 * vonMangoldt n := fun n =>
    le_trans (Finset.single_le_sum (f := fun g => 𝓕.lam g n) (fun g _ => 𝓕.lam_nonneg g n)
      (Finset.mem_univ _)) (𝓕.lam_le n)
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun n : ℕ => n.Prime)]
  apply add_le_add
  · have h1 : ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊).filter (fun n : ℕ => n.Prime), 𝓕.lam 0 n =
        ∑ n ∈ GlobalTheory.Mem.An.normPrimes d M X Y, 𝓕.lam 0 n := by
      symm
      apply Finset.sum_subset
      · intro p hp
        simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1⟩
      · intro p hp hq
        simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter] at hp hq
        by_contra h
        exact hq ⟨hp.1, hp.2, hN p hp.2 h⟩
    rw [h1, mul_comm, ← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    have h2 : (p : ℝ) ≤ Y := (Nat.le_floor_iff (by linarith)).1 hp.1.2
    have h3 : Real.log p ≤ Real.log Y :=
      Real.log_le_log (by exact_mod_cast hp.2.1.pos) h2
    have h4 := hl p
    rw [vonMangoldt_apply_prime hp.2.1] at h4
    linarith
  · rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun n _ => hl n) ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left (Nat.zero_le _))
    · intro n _ _
      have := @vonMangoldt_nonneg n
      positivity

theorem sqrt_le_short_main {A K c B X h : ℝ} (hA : 0 < A) (hK : 0 < K) (hc : 0 < c)
    (hcT : c ≤ 1 / (2 * (1 + A) + 2 + K)) (hB : 4 ≤ B) (hX : 1 ≤ X)
    (hBX : Real.log B ≤ c * Real.sqrt (Real.log X))
    (hh : Real.exp (-c * Real.sqrt (Real.log X)) ≤ h) :
    1 ≤ Real.log X ∧ K * Real.sqrt X ≤ h * X / B ^ A := by
  set s := Real.sqrt (Real.log X) with hs
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log X := Real.mul_self_sqrt hL
  have hB0 : 0 < B := by linarith
  have hB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  set T := 2 * (1 + A) + 2 + K with hT
  have hT0 : 0 < T := by positivity
  have hcT' : c * T ≤ 1 := by rwa [le_div_iff₀ hT0] at hcT
  have hsT : T ≤ s := by
    by_contra h'
    have : c * s < c * T := mul_lt_mul_of_pos_left (not_le.1 h') hc
    linarith
  have hc1 : c ≤ 1 := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  refine ⟨by nlinarith, ?_⟩
  have hX0 : 0 < X := by linarith
  have hsq : Real.sqrt X = Real.exp (s * s / 2) := by
    rw [hss, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]
    congr 1; ring
  have hXe : X = Real.exp (s * s) := by rw [hss, Real.exp_log hX0]
  have hcs : c * s ≤ s := by nlinarith
  have hBA : B ^ A ≤ Real.exp (A * s) := by
    rw [Real.rpow_def_of_pos hB0]
    apply Real.exp_le_exp.2
    nlinarith
  have hh' : Real.exp (-s) ≤ h := le_trans (Real.exp_le_exp.2 (by linarith)) hh
  have hKe : K ≤ Real.exp (s * s / 2 - (1 + A) * s) := by
    have := Real.add_one_le_exp (s * s / 2 - (1 + A) * s)
    have h5 : s * 1 ≤ s * (s / 2 - (1 + A)) := mul_le_mul_of_nonneg_left (by linarith) hs0
    nlinarith
  have hBA0 : 0 < B ^ A := Real.rpow_pos_of_pos hB0 A
  rw [le_div_iff₀ hBA0, hsq]
  calc K * Real.exp (s * s / 2) * B ^ A
      ≤ Real.exp (s * s / 2 - (1 + A) * s) * Real.exp (s * s / 2) * Real.exp (A * s) := by
        gcongr
    _ = Real.exp (-s) * Real.exp (s * s) := by
        simp only [← Real.exp_add]; congr 1; ring
    _ ≤ h * X := by
        rw [← hXe]; gcongr

theorem normPrimes_short_interval_lower : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X → Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) := by
  obtain ⟨A, c₀, e, hA, hc₀, he, H⟩ := GlobalTheory.T.exists_lam_zero_sum_shortInterval_ge
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set K : ℝ := 8 * (|C| + 1) / e with hKdef
  have hK : 0 < K := by positivity
  refine ⟨A, min c₀ (1 / (2 * (1 + A) + 2 + K)), e / 8, hA, lt_min hc₀ (by positivity),
    by positivity, ?_⟩
  intro d M X h hd hd4 hd100 hM hX hB hh hh1
  obtain ⟨𝓕, hFB, hN⟩ := GlobalTheory.T.exists_lFam_normOne_of_mod_four_eq_three d M hd hd4 hd100 hM
  rw [← hFB] at hB ⊢
  set c := min c₀ (1 / (2 * (1 + A) + 2 + K)) with hc
  have hc0 : 0 < c := lt_min hc₀ (by positivity)
  have hcc : c * Real.sqrt (Real.log X) ≤ c₀ * Real.sqrt (Real.log X) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
  have h0 : 0 < h := lt_of_lt_of_le (Real.exp_pos _) hh
  have H1 := H 𝓕 X h hX (hB.trans hcc) (le_trans (Real.exp_le_exp.2 (by linarith)) hh) hh1
  obtain ⟨hL, hS⟩ := sqrt_le_short_main hA hK hc0 (min_le_right _ _) 𝓕.B_ge hX hB hh
  have hY1 : 1 ≤ X * (1 + h) := by nlinarith
  have hY2 : X * (1 + h) ≤ 2 * X := by nlinarith
  have H2 := sum_lam_zero_le_card_normPrimes 𝓕 d M hN X (X * (1 + h)) hY1
  have hlog : Real.log (X * (1 + h)) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by linarith) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + h by linarith)
    linarith
  have hsq : Real.sqrt (X * (1 + h)) ≤ 2 * Real.sqrt X := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by linarith)]
    linarith
  have H3 : Chebyshev.psi (X * (1 + h)) - Chebyshev.theta (X * (1 + h)) ≤
      (|C| + 1) * (2 * Real.sqrt X) := by
    refine (hC _).trans ?_
    have := le_abs_self C
    have := abs_nonneg C
    have := Real.sqrt_nonneg (X * (1 + h))
    gcongr
    linarith
  have hBA0 : 0 < 𝓕.B ^ A := Real.rpow_pos_of_pos (by linarith [𝓕.B_ge]) A
  set N : ℝ := ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have H4 : 8 * (|C| + 1) * Real.sqrt X ≤ e * (h * X / 𝓕.B ^ A) := by
    have : 8 * (|C| + 1) * Real.sqrt X = e * (K * Real.sqrt X) := by
      rw [hKdef]; field_simp
    rw [this]; gcongr
  have H5 : e * h * X / 𝓕.B ^ A = e * (h * X / 𝓕.B ^ A) := by ring
  have H6 : 2 * Real.log (X * (1 + h)) * N ≤ 4 * Real.log X * N := by
    apply mul_le_mul_of_nonneg_right _ hN0
    linarith
  have H7 : e / 8 * h * X / (𝓕.B ^ A * Real.log X) = e * (h * X / 𝓕.B ^ A) / (8 * Real.log X) := by
    field_simp
  rw [H7, div_le_iff₀ (by linarith)]
  linarith

end GlobalTheory.Hk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBoundStatement

section

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X → Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) := by
  first | exact @GlobalTheory.Hk.normPrimes_short_interval_lower | exact GlobalTheory.Hk.normPrimes_short_interval_lower | (intros; apply GlobalTheory.Hk.normPrimes_short_interval_lower <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ShortNorms.SmallOneOf

section

@[expose] public section

open GlobalTheory.Mem.An

namespace UpperTheory.T3

theorem smallOne_of :
    GlobalTheory.Lin.PrimesRel → SmallOne := by
  intro hP
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, hI⟩ := GlobalTheory.Lin.primesAPInterval_of_primesRel hP
  obtain ⟨N, hN⟩ := exists_nat_ge (max (max C₀ 21) (Real.log (200 * Cr) / cr))
  have hN21 : (21:ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNC : C₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNl : Real.log (200 * Cr) / cr ≤ N := le_trans (le_max_right _ _) hN
  set K : ℝ := (N:ℝ) ^ 2 with hK
  have hNK : (N:ℝ) ≤ K := by nlinarith
  have hK0 : 0 ≤ K := by positivity
  refine ⟨3 * K + 1, by linarith, ?_⟩
  intro M hM
  rcases Nat.lt_or_ge M 3 with hM3 | hM3
  · have hM2 : M = 2 := by omega
    subst hM2
    refine ⟨3, Nat.prime_three, by norm_num, ?_⟩
    have h1 : ((2:ℕ):ℝ) ^ (2:ℝ) ≤ ((2:ℕ):ℝ) ^ (3 * K + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
    have h2 : ((2:ℕ):ℝ) ^ (2:ℝ) = 4 := by norm_num
    push_cast at h1 h2 ⊢
    linarith
  · have hMr : (3:ℝ) ≤ M := by exact_mod_cast hM3
    set B : ℝ := 4 * (M:ℝ) with hB
    have hB12 : (12:ℝ) ≤ B := by linarith
    have hB0 : 0 < B := by linarith
    have hlogB : 1 ≤ Real.log B := by
      rw [Real.le_log_iff_exp_le hB0]
      have := Real.exp_one_lt_d9
      linarith
    set Y : ℝ := B ^ K with hY
    have hY0 : 0 < Y := Real.rpow_pos_of_pos hB0 _
    have hlogY : Real.log Y = K * Real.log B := Real.log_rpow hB0 K
    have hlogY0 : 0 < Real.log Y := by rw [hlogY]; nlinarith
    have hexp : Real.exp (-cr * N) ≤ 1 / (200 * Cr) := by
      have h1 : Real.log (200 * Cr) ≤ cr * N := by
        rw [div_le_iff₀ hcr] at hNl; linarith
      have h2 : Real.exp (Real.log (200 * Cr)) ≤ Real.exp (cr * N) := Real.exp_le_exp.mpr h1
      rw [Real.exp_log (by positivity)] at h2
      rw [show -cr * (N:ℝ) = -(cr * N) by ring, Real.exp_neg, one_div]
      exact inv_anti₀ (by positivity) h2
    have hρ : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Y ≤ 1 / 100 := by
      unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
      have e1 : Real.exp (-cr * Real.log Y / Real.log B) ≤ Real.exp (-cr * N) := by
        apply Real.exp_le_exp.mpr
        rw [hlogY, show -cr * (K * Real.log B) / Real.log B = -cr * K by field_simp]
        nlinarith
      have e2 : Real.exp (-cr * √(Real.log Y)) ≤ Real.exp (-cr * N) := by
        apply Real.exp_le_exp.mpr
        have : (N:ℝ) ≤ √(Real.log Y) := by
          rw [show (N:ℝ) = √K by rw [hK, Real.sqrt_sq (by positivity)]]
          apply Real.sqrt_le_sqrt
          rw [hlogY]; nlinarith
        nlinarith
      have e3 : Cr * Real.exp (-cr * N) ≤ 1 / 200 := by
        have := mul_le_mul_of_nonneg_left hexp hCr.le
        rw [show Cr * (1 / (200 * Cr)) = 1 / 200 by field_simp] at this
        exact this
      nlinarith [mul_le_mul_of_nonneg_left e1 hCr.le, mul_le_mul_of_nonneg_left e2 hCr.le]
    have hc1 : B ^ C₀ ≤ Y := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hc3 : B ^ (7:ℝ) ≤ 1 * Y ^ ((1:ℝ) / 3) := by
      rw [one_mul, hY, ← Real.rpow_mul hB0.le]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
    have hmain := hI M 1 hM3 (Nat.coprime_one_left M) Y 1 hc1 le_rfl (by simpa using hρ) hc3
    have hpos : 0 < c * 1 * B ^ (-6:ℝ) * Y / Real.log Y := by
      have := Real.rpow_pos_of_pos hB0 (-6:ℝ)
      positivity
    have hcard : 0 < ({p ∈ Finset.Ioc ⌊Y⌋₊ ⌊Y * (1 + 1)⌋₊ | Nat.Prime p ∧ p ≡ 1 [MOD M]}).card := by
      have := lt_of_lt_of_le hpos hmain
      exact_mod_cast this
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨_, hpY⟩, hpp, hpm⟩ := hp
    refine ⟨p, hpp, ?_, ?_⟩
    · have : 1 % M = 1 := Nat.mod_eq_of_lt (by omega)
      rw [← this]; exact hpm
    · have hp2 : (p:ℝ) ≤ 2 * Y := by
        have := Nat.floor_le (show 0 ≤ Y * (1 + 1) by positivity)
        have h' : (p:ℝ) ≤ (⌊Y * (1 + 1)⌋₊ : ℝ) := by exact_mod_cast hpY
        linarith
      have hBM : B ≤ (M:ℝ) ^ (3:ℝ) := by
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast, hB]
        have h9 : (9:ℝ) ≤ (M:ℝ) ^ 2 := by nlinarith
        nlinarith
      have hM0 : (0:ℝ) < M := by linarith
      have hYM : Y ≤ (M:ℝ) ^ (3 * K) := by
        rw [hY, Real.rpow_mul hM0.le]
        exact Real.rpow_le_rpow hB0.le hBM hK0
      rw [Real.rpow_add hM0, Real.rpow_one]
      have : 0 < (M:ℝ) ^ (3 * K) := Real.rpow_pos_of_pos hM0 _
      nlinarith

end UpperTheory.T3
end
end

-- Source module: Development.AutomorphicArithmetic.ShortNorms.Primes

section

@[expose] public section

theorem UpperTheory.T3.shortNorm : UpperTheory.T3.ShortNorm := GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound

theorem UpperTheory.T3.smallOne : UpperTheory.T3.SmallOne := UpperTheory.T3.smallOne_of GlobalTheory.T.primesInProgressions_relativeError
end
end
