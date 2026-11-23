module

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ChebyshevCharacterExplicitGeneral
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

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExpGainFromZeroFreeRegion

section

@[expose] public section

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem perron_error_terms_sum_bound (C C₀ c₁ y T X L Pw Y ℓ : ℝ) (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hy0 : 0 < y) (hT1 : 1 ≤ T) (hTX : T * X = 1) (hL0 : 0 ≤ L) (hY : 0 ≤ Y)
    (hℓP : ℓ ≤ Pw) (hP1 : 1 ≤ Pw) (hL2P : L ^ 2 ≤ Pw) (hL3P : L ^ 3 ≤ Pw) (hLP : L ≤ Pw) :
    2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T)
        + Y * (8 * L / c₁) ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
        16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁) * Pw * (y * X + T * Y) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by nlinarith
  have hX1 : X ≤ 1 := by nlinarith
  have e1 : ∀ z : ℝ, z / T = z * X := fun z => by
    rw [div_eq_iff hT0.ne', mul_assoc, mul_comm X T, hTX, mul_one]
  have e2 : ∀ z : ℝ, z / T ^ 2 = z * X * X := fun z => by
    rw [div_eq_iff (pow_pos hT0 2).ne']
    calc z = z * (T * X) * (T * X) := by rw [hTX]; ring
      _ = z * X * X * T ^ 2 := by ring
  simp only [e1, e2]
  have hPw : 0 ≤ Pw := by linarith
  have hyX : 0 ≤ y * X := mul_nonneg hy0.le hX0.le
  have hTY : 0 ≤ T * Y := mul_nonneg hT0.le hY
  have hcC : 0 ≤ C / c₁ := div_nonneg hC hc₁.le
  have hc2 : 0 ≤ 24 / c₁ ^ 2 := by positivity
  have h8 : 0 ≤ 8 / c₁ := div_nonneg (by norm_num) hc₁.le
  have k1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
  have k2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
  have k3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) := mul_nonneg (by norm_num) (add_nonneg hcC hc2)
  have h1 : 2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) * X ≤
      2 * Real.pi * Real.exp 1 * (1 + C₀) * Pw * (y * X) := by
    have hA : ℓ + C₀ ≤ (1 + C₀) * Pw := by nlinarith
    have hk : 0 ≤ 2 * Real.pi * Real.exp 1 * (y * X) := mul_nonneg (by positivity) hyX
    have := mul_le_mul_of_nonneg_left hA hk
    linarith
  have hB0 : 0 ≤ C * L ^ 2 + 1 := add_nonneg (mul_nonneg hC (sq_nonneg L)) zero_le_one
  have hB : C * L ^ 2 + 1 ≤ (C + 1) * Pw := by
    linarith [mul_le_mul_of_nonneg_left hL2P hC]
  have hXX : X * X ≤ X := mul_le_of_le_one_right hX0.le hX1
  have h2 : (C * L ^ 2 + 1) * (Real.exp 1 * y) * X * X * 3 ≤ 3 * Real.exp 1 * (C + 1) * Pw * (y * X) := by
    have s1 : (C * L ^ 2 + 1) * (X * X) ≤ (C * L ^ 2 + 1) * X := mul_le_mul_of_nonneg_left hXX hB0
    have s2 : (C * L ^ 2 + 1) * X ≤ (C + 1) * Pw * X := mul_le_mul_of_nonneg_right hB hX0.le
    have s3 := mul_le_mul_of_nonneg_left (s1.trans s2)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (mul_nonneg (Real.exp_pos 1).le hy0.le))
    linarith
  have h3 : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) ≤
      16 * (C / c₁ + 24 / c₁ ^ 2) * Pw * (T * Y) := by
    have hid : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) =
        (16 * (C / c₁) * L ^ 3 + 16 * (24 / c₁ ^ 2) * L ^ 2) * (T * Y) := by ring
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ hTY
    linarith [mul_le_mul_of_nonneg_left hL3P hcC, mul_le_mul_of_nonneg_left hL2P hc2]
  have h4 : Y * (8 * L / c₁) ≤ 8 / c₁ * Pw * (T * Y) := by
    have hid : Y * (8 * L / c₁) = 8 / c₁ * L * Y := by ring
    rw [hid]
    have s1 : 8 / c₁ * L ≤ 8 / c₁ * Pw := mul_le_mul_of_nonneg_left hLP h8
    have s2 : Y ≤ T * Y := by nlinarith
    calc 8 / c₁ * L * Y ≤ 8 / c₁ * Pw * Y := mul_le_mul_of_nonneg_right s1 hY
      _ ≤ 8 / c₁ * Pw * (T * Y) := mul_le_mul_of_nonneg_left s2 (mul_nonneg h8 hPw)
  nlinarith [mul_nonneg (mul_nonneg k1 hPw) hTY, mul_nonneg (mul_nonneg k2 hPw) hTY,
    mul_nonneg (mul_nonneg k3 hPw) hyX, mul_nonneg (mul_nonneg h8 hPw) hyX]

theorem exp_gain_from_zero_free_region (y s c₁ σ₁ L : ℝ) (hy0 : 0 < y) (hℓ : Real.log y = s ^ 2) (hs0 : 0 < s)
    (hc₁ : 0 < c₁) (hL : 0 < L) (hL4 : 4 * L ≤ s) (hσ : σ₁ ≤ 1 - c₁ / (4 * L)) :
    Real.exp (c₁ * s / 2) * y ^ σ₁ ≤ y * Real.exp (-(c₁ * s / 2)) := by
  have hy : y = Real.exp (s ^ 2) := by rw [← hℓ, Real.exp_log hy0]
  have hyσ : y ^ σ₁ = Real.exp (s ^ 2 * σ₁) := by rw [Real.rpow_def_of_pos hy0, hℓ]
  rw [hyσ, ← Real.exp_add, hy, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h4L : 0 < 4 * L := by linarith
  have hq : c₁ ≤ c₁ / (4 * L) * s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h4L]; nlinarith
  have hc : c₁ ≤ (1 - σ₁) * s := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : c₁ / (4 * L) ≤ 1 - σ₁) hs0.le]
  nlinarith [mul_le_mul_of_nonneg_right hc hs0.le]

theorem small_scale_exp_bounds (c₁ s : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (hs : s < 10) :
    Real.exp (c₁ * s / 2) ≤ 3 ∧ 1 ≤ 3 * Real.exp (-(c₁ / 4) * s) := by
  constructor
  · have h : c₁ * s / 2 ≤ 1 := by nlinarith
    calc Real.exp (c₁ * s / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr h
      _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  · have h : -(1 / 8 : ℝ) ≤ -(c₁ / 4) * s := by nlinarith
    have := Real.add_one_le_exp (-(c₁ / 4) * s)
    linarith

theorem cube_mul_exp_le_poly_bound (c₁ s y X : ℝ) (hc₁ : 0 < c₁) (hs0 : 0 < s) (hy0 : 0 < y)
    (hX : X = Real.exp (-(c₁ * s / 2))) :
    s ^ 3 * X * y ≤ 6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s)) := by
  have hu0 : 0 < c₁ * s / 4 := div_pos (mul_pos hc₁ hs0) (by norm_num)
  have hexp : (c₁ * s / 4) ^ 3 / 6 ≤ Real.exp (c₁ * s / 4) := by
    have h := Real.pow_div_factorial_le_exp (c₁ * s / 4) hu0.le 3
    norm_num [Nat.factorial] at h
    linarith
  have hX' : X = Real.exp (-(c₁ * s / 4)) * Real.exp (-(c₁ * s / 4)) := by
    rw [hX, ← Real.exp_add]; congr 1; ring
  have he : Real.exp (-(c₁ / 4) * s) = Real.exp (-(c₁ * s / 4)) := by congr 1; ring
  rw [he, hX']
  have hu3 : (c₁ * s / 4) ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 := by
    have h2 : Real.exp (c₁ * s / 4) * Real.exp (-(c₁ * s / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_right (by linarith : (c₁ * s / 4) ^ 3 ≤ 6 * Real.exp (c₁ * s / 4))
      (Real.exp_pos (-(c₁ * s / 4))).le
    linarith
  have hsu : s = 8 / (2 * c₁) * (c₁ * s / 4) := by
    have := hc₁.ne'
    field_simp
    try ring
  have hK : 0 ≤ (8 / (2 * c₁)) ^ 3 := pow_nonneg (div_nonneg (by norm_num) (by linarith)) 3
  have key : s ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 * (8 / (2 * c₁)) ^ 3 := by
    have hs3 : s ^ 3 = (8 / (2 * c₁)) ^ 3 * (c₁ * s / 4) ^ 3 := by
      rw [← mul_pow, ← hsu]
    rw [hs3]
    nlinarith [mul_le_mul_of_nonneg_left hu3 hK]
  nlinarith [mul_le_mul_of_nonneg_right key (mul_pos (Real.exp_pos (-(c₁ * s / 4))) hy0).le]

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SmoothChiOf

section

@[expose] public section

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem smoothed_character_sum_of : SmoothChiOf := by
  intro hP hRS hD hRight c₁ hc₁ hc₁'
  obtain ⟨CD, hCD⟩ := hD c₁ hc₁ hc₁'
  obtain ⟨C₀, hC₀, hR⟩ := hRight
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max CD 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
      16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    have ha1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
    have ha2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
    have ha3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) :=
      mul_nonneg (by norm_num) (add_nonneg (div_nonneg hC hc₁.le) (by positivity))
    have ha4 : 0 ≤ 8 / c₁ := by positivity
    rw [hAdef]; linarith
  refine ⟨c₁ / 4, max (16 * A * (6 * (8 / (2 * c₁)) ^ 3)) (3 * (4 * 12 ^ 3 * A)), by positivity, ?_⟩
  intro q _ χ B y hχ hE hy hq
  have hD' : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
      ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 :=
    fun s h1 h2 => (hCD q χ B hχ hE s h1 h2).trans
      (mul_le_mul_of_nonneg_right (hCdef ▸ le_max_left _ _) (sq_nonneg _))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hℓpos : 0 < Real.log y := Real.log_pos (by linarith)
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (Real.log y) := ⟨_, rfl⟩
  rw [← hsdef] at hq ⊢
  have hℓ : Real.log y = s ^ 2 := by rw [hsdef]; exact (Real.sq_sqrt hℓpos.le).symm
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hℓpos
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp (c₁ * s / 2) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = Real.exp (-(c₁ * s / 2)) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp (by positivity)
  have hT0 : 0 < T := by linarith
  have hTX : T * X = 1 := by rw [hTdef, hXdef, ← Real.exp_add]; simp
  have hX0 : 0 < X := by rw [hXdef]; exact Real.exp_pos _
  have hX1 : X ≤ 1 := by
    rw [hXdef]; exact Real.exp_le_one_iff.mpr (by linarith [mul_pos hc₁ hs0])
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * (T + 2)) := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁, hmain⟩ :=
    chebyshev_character_explicit_general hP hRS c₁ C C₀ hc₁ hc₁' hC hC₀ χ B hχ hE hD' (hR q χ) y T L hy hT1 hLdef.symm

  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * (T + 2) := one_le_mul_of_one_le_of_one_le hq1 (by linarith)
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg hqT1
  have hlogq : Real.log q ≤ c₁ / 4 * s := (Real.log_le_iff_le_exp (by linarith)).mpr hq
  have hlogT : Real.log (T + 2) ≤ 2 + c₁ * s / 2 := by
    rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, ← hTdef]
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have := mul_le_mul_of_nonneg_right h3 hT0.le
    linarith
  have hLb : L ≤ 3 * c₁ / 4 * s + 2 := by
    rw [hLdef, Real.log_mul (by linarith) (by linarith)]
    linarith
  have hs'1 : 1 ≤ s + 2 := by linarith
  have hLs' : L ≤ s + 2 := by
    have : 3 * c₁ / 4 * s ≤ s := mul_le_of_le_one_left hs0.le (by linarith)
    linarith
  have hP1 : 1 ≤ (s + 2) ^ 3 := one_le_pow₀ hs'1
  have h23 : (s + 2) ^ 2 ≤ (s + 2) ^ 3 := pow_le_pow_right₀ hs'1 (by norm_num)
  have hℓP : Real.log y ≤ (s + 2) ^ 3 := by
    rw [hℓ]
    have h1 : s ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ hs0.le (by linarith) 2
    linarith
  have hL2P : L ^ 2 ≤ (s + 2) ^ 3 := by
    have h1 : L ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ hL0 hLs' 2
    linarith
  have hL3P : L ^ 3 ≤ (s + 2) ^ 3 := pow_le_pow_left₀ hL0 hLs' 3
  have hLP : L ≤ (s + 2) ^ 3 := by
    have : s + 2 ≤ (s + 2) ^ 3 := le_self_pow₀ hs'1 (by norm_num)
    linarith
  have hyσ0 : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
  have hterms := perron_error_terms_sum_bound C C₀ c₁ y T X L ((s + 2) ^ 3) (y ^ σ₁) (Real.log y) hc₁ hC hC₀ hy0
    hT1 hTX hL0 hyσ0 hℓP hP1 hL2P hL3P hLP
  rw [← hAdef] at hterms
  have htot := hmain.trans hterms
  have hyX : 0 ≤ y * X := by positivity
  by_cases hs : 10 ≤ s
  ·
    have hL4 : 4 * L ≤ s := by
      have := mul_le_mul_of_nonneg_right hc₁' hs0.le
      linarith
    have hLpos : 0 < L := by
      rw [hLdef]; apply Real.log_pos
      have := mul_le_mul hq1 (show (3 : ℝ) ≤ T + 2 by linarith) (by norm_num) (by linarith)
      linarith
    have hWX : T * y ^ σ₁ ≤ y * X := by
      rw [hTdef, hXdef]; exact exp_gain_from_zero_free_region y s c₁ σ₁ L hy0 hℓ hs0 hc₁ hLpos hL4 hσ₁
    have hs'2 : (s + 2) ^ 3 ≤ 8 * s ^ 3 := by
      calc (s + 2) ^ 3 ≤ (2 * s) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
        _ = 8 * s ^ 3 := by ring
    have hX3 := cube_mul_exp_le_poly_bound c₁ s y X hc₁ hs0 hy0 hXdef
    calc _ ≤ A * (s + 2) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * (8 * s ^ 3) * (y * X + y * X) := by gcongr
      _ = 16 * A * (s ^ 3 * X * y) := by ring
      _ ≤ 16 * A * (6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s))) := by gcongr
      _ = 16 * A * (6 * (8 / (2 * c₁)) ^ 3) * y * Real.exp (-(c₁ / 4) * s) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  ·
    rw [not_le] at hs
    obtain ⟨hT3', hexp⟩ := small_scale_exp_bounds c₁ s hc₁ hc₁' hs
    have hT3 : T ≤ 3 := hTdef ▸ hT3'
    have hPs : (s + 2) ^ 3 ≤ 12 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hσ₁1 : σ₁ ≤ 1 := by
      have : 0 ≤ c₁ / (4 * L) := by positivity
      linarith
    have hyσ : y ^ σ₁ ≤ y := by
      have := Real.rpow_le_rpow_of_exponent_le hy1 hσ₁1
      rwa [Real.rpow_one] at this
    have hW3 : T * y ^ σ₁ ≤ 3 * y := mul_le_mul hT3 hyσ hyσ0 (by norm_num)
    have hyX1 : y * X ≤ y := mul_le_of_le_one_right hy0.le hX1
    calc _ ≤ A * (s + 2) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * 12 ^ 3 * (y + 3 * y) := by gcongr
      _ = 4 * 12 ^ 3 * A * y * 1 := by ring
      _ ≤ 4 * 12 ^ 3 * A * y * (3 * Real.exp (-(c₁ / 4) * s)) := by gcongr
      _ = 3 * (4 * 12 ^ 3 * A) * y * Real.exp (-(c₁ / 4) * s) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end Formalism.ZeroFreeDirichlet
end
end
end
