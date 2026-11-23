module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplDefs
public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronHorizontalSegmentBound
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMainA
public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLF
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLocL
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
import Mathlib.Tactic.Lemma
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectF
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplEdge

section

@[expose] public section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_left_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ T' B : ℝ) (hy : 1 ≤ y)
    (hσ : 1 / 2 ≤ σ₁) (hσ1 : σ₁ < 1) (hT' : 0 ≤ T')
    (hB : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ B) :
    ‖∫ t in (-T')..T', Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ 2 * T' * B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
  have hy0 : 0 < y := by linarith
  have hσp : 0 < σ₁ := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hT'))
  have hpt : ∀ t ∈ Set.uIoc (-T') T', ‖Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hBt := hB t (abs_le.mpr ⟨ht.1.le, ht.2⟩)
    set w : ℂ := (σ₁ : ℂ) + (t : ℂ) * I with hw
    have hre : w.re = σ₁ := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : σ₁ ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      rw [hre, abs_of_pos hσp] at this; exact this
    have hw2 : 1 - σ₁ ≤ ‖w - 1‖ := by
      have h1 : (w - 1).re = σ₁ - 1 := by simp [hre]
      have := Complex.abs_re_le_norm (w - 1)
      rw [h1, abs_of_neg (by linarith)] at this; linarith
    have hden : σ₁ * (1 - σ₁) ≤ ‖w‖ * ‖w - 1‖ :=
      mul_le_mul hw1 hw2 (by linarith) (norm_nonneg _)
    have hdp : 0 < σ₁ * (1 - σ₁) := mul_pos hσp (by linarith)
    have hyp : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ σ₁ / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₁ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) :=
          div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) hdp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  have : |T' - -T'| = 2 * T' := by rw [abs_of_nonneg (by linarith)]; ring
  rw [this]; ring

theorem ex_horiz_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ σ₀ v B : ℝ) (hy : 1 ≤ y)
    (hσ : σ₁ ≤ σ₀) (hv : 1 ≤ |v|) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ B) :
    ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤ (σ₀ - σ₁) * B * y ^ σ₀ / v ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hpt : ∀ x ∈ Set.uIoc σ₁ σ₀, ‖Fchi χ y ((x : ℂ) + v * I)‖ ≤ B * y ^ σ₀ / v ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hσ] at hx
    have hBx := hB x hx.1.le hx.2
    set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
    have hre : w.re = x := by simp [hw]
    have him : w.im = v := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : |v| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
    have hw2 : |v| ≤ ‖w - 1‖ := by
      have : (w - 1).im = v := by simp [him]
      rw [← this]; exact Complex.abs_im_le_norm _
    have hpow : y ^ x ≤ y ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hy hx.2
    have hden : v ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
      rw [← sq_abs]; nlinarith [abs_nonneg v]
    have htp : 0 < v ^ 2 := by rw [← sq_abs]; positivity
    have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ x / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₀ / v ^ 2 := div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) htp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  rw [abs_of_nonneg (by linarith)]; ring

theorem ex_tail_half (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T)
    (hf : ∀ t : ℝ, T < t → ‖f t‖ ≤ K / t ^ 2) :
    ‖∫ t in Set.Ioi T, f t‖ ≤ K / T := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have h := MeasureTheory.norm_integral_le_of_norm_le (μ := MeasureTheory.volume.restrict (Set.Ioi T))
    (f := f) hint
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => by
      have ht0 : 0 < t := lt_trans hT ht
      have := hf t ht
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      simpa [div_eq_mul_inv] using this)))
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
  have : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp

theorem ex_tail_gen (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T) (hi : MeasureTheory.Integrable f)
    (hf : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ K / t ^ 2) :
    ‖(∫ t : ℝ, f t) - ∫ t in (-T)..T, f t‖ ≤ 2 * K / T := by
  have h1 : (∫ t in Set.Iic (-T), f t) + ∫ t in Set.Ioi (-T), f t = ∫ t : ℝ, f t :=
    intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn
  have h2 : (∫ t in (-T)..T, f t) + ∫ t in Set.Ioi T, f t = ∫ t in Set.Ioi (-T), f t :=
    intervalIntegral.integral_interval_add_Ioi hi.integrableOn hi.integrableOn
  have h3 : (∫ t in Set.Ioi T, f (-t)) = ∫ t in Set.Iic (-T), f t := integral_comp_neg_Ioi T f
  have e : (∫ t : ℝ, f t) - ∫ t in (-T)..T, f t
      = (∫ t in Set.Ioi T, f (-t)) + ∫ t in Set.Ioi T, f t := by
    rw [← h1, ← h2, h3]; ring
  rw [e]
  have a := ex_tail_half (fun t => f (-t)) K T hT (fun t ht => by
    have := hf (-t) (by rw [abs_neg]; exact lt_of_lt_of_le ht (le_abs_self t))
    simpa using this)
  have b := ex_tail_half f K T hT (fun t ht => hf t (lt_of_lt_of_le ht (le_abs_self t)))
  calc _ ≤ ‖∫ t in Set.Ioi T, f (-t)‖ + ‖∫ t in Set.Ioi T, f t‖ := norm_add_le _ _
    _ ≤ K / T + K / T := add_le_add a b
    _ = 2 * K / T := by ring

theorem ex_tail_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₀ T' : ℝ),
    1 ≤ y → 1 < σ₀ → 1 ≤ T' →
    ‖(∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + t * I)) - ∫ t in (-T')..T', Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * (1 / (σ₀ - 1) + C) * y ^ σ₀ / T' := by
  obtain ⟨C, hC, hR⟩ := l_log_deriv_right
  refine ⟨C, hC, ?_⟩
  intro M _ χ y σ₀ T' hy hσ hT'
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T' := by linarith
  obtain ⟨hint, -⟩ := perron_formula_character M χ y hy σ₀ hσ
  have h := ex_tail_gen (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) ((1 / (σ₀ - 1) + C) * y ^ σ₀) T' hT0 hint
    (fun t ht => by
      have ht0 : 0 < |t| := lt_trans hT0 ht
      show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _
      set w : ℂ := (σ₀ : ℂ) + (t : ℂ) * I with hw
      have hre : w.re = σ₀ := by simp [hw]
      have him : w.im = t := by simp [hw]
      rw [norm_perron_integrand_eq χ y hy0 w, hre]
      have hζ : ‖negLD χ w‖ ≤ 1 / (σ₀ - 1) + C := by
        have := hR M χ w (by rw [hre]; exact hσ)
        rwa [hre] at this
      have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
      have hw2 : |t| ≤ ‖w - 1‖ := by
        have : (w - 1).im = t := by simp [him]
        rw [← this]; exact Complex.abs_im_le_norm _
      have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      have htp : 0 < t ^ 2 := by rw [← sq_abs]; positivity
      have hnum : 0 ≤ 1 / (σ₀ - 1) + C := le_trans (norm_nonneg _) hζ
      have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
      calc ‖negLD χ w‖ * y ^ σ₀ / (‖w‖ * ‖w - 1‖)
          ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
        _ ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / t ^ 2 :=
            div_le_div_of_nonneg_left (mul_nonneg hnum hyp) htp hden)
  refine h.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplNeg

section

@[expose] public section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

lemma ex_sum_le {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)

lemma ex_one_le_log {M : ℕ} (hM : 3 ≤ M) (t : ℝ) : 1 ≤ Real.log ((M : ℝ) * (|t| + 2)) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h0 := abs_nonneg t
  have h6 : (6 : ℝ) ≤ (M : ℝ) * (|t| + 2) := by nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem ex_negLD_bound : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ) (δ : ℝ),
    3 ≤ M → 0 < δ → δ ≤ 1 / 20 → 19 / 20 ≤ s.re → s.re ≤ 3 → s ≠ 1 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → ‖ρ - s‖ ≤ 1 / 5 → δ ≤ ‖ρ - s‖) →
    ‖negLD χ s‖ ≤ C * Real.log ((M : ℝ) * (|s.im| + 2)) / δ + (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
  obtain ⟨C₀, hC₀, hR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  obtain ⟨C₁, hC₁, hloc⟩ := ex_local
  refine ⟨2 * C₁ + (100 / 7 + C₀), by positivity, ?_⟩
  intro M _ χ s δ hM hδ hδ' hs1 _ hsne hz
  set large₂ : ℝ := Real.log ((M : ℝ) * (|s.im| + 2)) with hLg
  have hL1 : 1 ≤ large₂ := ex_one_le_log hM s.im
  have hif : (0 : ℝ) ≤ (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
    split_ifs
    · positivity
    · exact le_rfl

  have hup : ∀ x : ℝ, 0 ≤ x → x ≤ x * large₂ / δ := by
    intro x hx
    rw [le_div_iff₀ hδ]
    have : x * δ ≤ x * 1 := mul_le_mul_of_nonneg_left (by linarith) hx
    have h2 : x * 1 ≤ x * large₂ := mul_le_mul_of_nonneg_left hL1 hx
    linarith
  by_cases hcase : 107 / 100 ≤ s.re
  · have h1 := hR M χ s (by linarith)
    have h2 : 1 / (s.re - 1) ≤ 100 / 7 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 := hup (2 * C₁ + (100 / 7 + C₀)) (by positivity)
    linarith
  · rw [not_le] at hcase
    obtain ⟨Z, hZ, hcard, hexp⟩ := hloc M χ s.im hM
    have hne : exLF χ s ≠ 0 := by
      intro h0
      have := hz s h0 (by linarith) (by simp)
      simp at this
      linarith
    have hsb : s ∈ Metric.closedBall ((101 / 100 : ℂ) + s.im * I) (1 / 15) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : s - ((101 / 100 : ℂ) + s.im * I) = ((s.re - 101 / 100 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hE := hexp s hsb hne
    have hdist : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖ := by
      intro ρ hρ
      obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
      rw [norm_sub_rev]
      by_cases h9 : 9 / 10 ≤ ρ.re
      · refine hz ρ hρ0 h9 ?_
        rw [Metric.mem_closedBall] at hρb hsb
        have := dist_triangle_right ρ s ((101 / 100 : ℂ) + s.im * I)
        rw [dist_eq_norm] at this
        linarith
      · rw [not_le] at h9
        have := Complex.abs_re_le_norm (ρ - s)
        rw [Complex.sub_re] at this
        have h3 := neg_abs_le (ρ.re - s.re)
        linarith
    have hS := ex_sum_le hδ Z (exOrd χ) s hdist
    have hS2 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) / δ ≤ C₁ * large₂ / δ :=
      div_le_div_of_nonneg_right hcard hδ.le
    have hD : ‖deriv (exLF χ) s / exLF χ s‖ ≤ C₁ * large₂ + C₁ * large₂ / δ := by
      have := norm_sub_norm_le (deriv (exLF χ) s / exLF χ s) (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ))
      linarith
    have hCL : C₁ * large₂ ≤ C₁ * large₂ / δ := by
      rw [le_div_iff₀ hδ]
      have : 0 ≤ C₁ * large₂ := by positivity
      nlinarith
    have hI : ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ = (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
      split_ifs <;> simp
    rw [negLD_eq_exLF χ hsne hne]
    have hN := norm_sub_le (if χ = 1 then 1 / (s - 1) else 0 : ℂ) (deriv (exLF χ) s / exLF χ s)
    rw [hI] at hN
    have hex : (2 * C₁ + (100 / 7 + C₀)) * large₂ / δ = 2 * (C₁ * large₂ / δ) + (100 / 7 + C₀) * large₂ / δ := by ring
    have hpos : 0 ≤ (100 / 7 + C₀) * large₂ / δ := by positivity
    rw [hex]
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end

-- Source module: Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMainB

section

@[expose] public section

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem exm_neg {C₂ : ℝ} (hC₂ : 0 < C₂) {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (T δ E : ℝ) (s : ℂ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hδ0 : 0 < δ) (him : |s.im| ≤ T + 1) (hE : 1 / ‖s - 1‖ ≤ E) (hE0 : 0 ≤ E)
    (h : ‖negLD χ s‖ ≤ C₂ * Real.log ((M : ℝ) * (|s.im| + 2)) / δ + (if χ = 1 then 1 / ‖s - 1‖ else 0)) :
    ‖negLD χ s‖ ≤ C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + E := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 := exm_log_le (M : ℝ) T |s.im| hM' hT (abs_nonneg _) him
  have h2 : (if χ = 1 then 1 / ‖s - 1‖ else 0) ≤ E := by split_ifs <;> assumption
  refine h.trans (add_le_add ?_ h2)
  gcongr

theorem exm_rpow_sigma (y : ℝ) (hy : 2 ≤ y) : y ^ (1 + 1 / Real.log y) = Real.exp 1 * y := by
  have hy0 : 0 < y := by linarith
  have hl := exm_log_y y hy
  have hl0 : Real.log y ≠ 0 := by linarith
  rw [Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0, mul_one_div_cancel hl0, mul_comm]

theorem exm_core : ∃ C₂ C₃ : ℝ, 0 < C₂ ∧ 0 ≤ C₃ ∧ ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T σ₁ T' δ : ℝ), 3 ≤ M → 2 ≤ T →
    1 - κ ≤ σ₁ → σ₁ ≤ 1 - 3 * κ / 4 → T ≤ T' → T' ≤ T + 1 → 0 < δ → δ ≤ 1 / 20 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) →
    ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T')) →
    ∀ y : ℝ, 2 ≤ y →
      ‖Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - explicitFormulaConstant χ - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
        1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T' +
          2 * T' * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁)) +
          (3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2 +
           3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2)) := by
  obtain ⟨C₂, hC₂, hneg⟩ := ex_negLD_bound
  obtain ⟨C₃, hC₃, htail⟩ := ex_tail_bound
  refine ⟨C₂, C₃, hC₂, hC₃, ?_⟩
  intro κ hκ hκ' M _ χ T σ₁ T' δ hM hT hσ hσ' hTT' hT'T hδ0 hδ' hgapre hgapim Z hZ y hy
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hy0 : 0 < y := by linarith
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have hly := exm_log_y y hy
  have hl1 := exm_log_ge_one (M : ℝ) T hM' hT
  set N := C₂ * (2 * Real.log ((M : ℝ) * T)) / δ with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  set σ₀ := 1 + 1 / Real.log y with hσ₀
  have hσ₀1 : 1 < σ₀ := by
    have : 0 < 1 / Real.log y := by positivity
    linarith
  have hσ₀3 : σ₀ ≤ 3 := by
    have : 1 / Real.log y ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hly
    rw [hσ₀]; linarith
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := exm_rpow_sigma y hy
  have hσ19 : 19 / 20 ≤ σ₁ := by linarith
  have hσ1 : σ₁ < 1 := by linarith
  have hT'0 : 0 < T' := by linarith

  have hBL : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ N + 4 / (3 * κ) := by
    intro t ht
    have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
    have him : ((σ₁ : ℂ) + t * I).im = t := by simp
    have hnorm : 3 * κ / 4 ≤ ‖(σ₁ : ℂ) + t * I - 1‖ := by
      have h1 := Complex.abs_re_le_norm ((σ₁ : ℂ) + t * I - 1)
      have h2 : ((σ₁ : ℂ) + t * I - 1).re = σ₁ - 1 := by simp
      rw [h2, abs_of_neg (by linarith)] at h1
      linarith
    have hne : (σ₁ : ℂ) + t * I ≠ 1 := by
      intro h
      rw [h] at hnorm
      simp at hnorm
      linarith
    apply exm_neg hC₂ χ T δ _ _ hM hT hδ0 (by rw [him]; linarith) _ (by positivity)
    · apply hneg M χ _ δ hM hδ0 hδ' (by rw [hre]; exact hσ19) (by rw [hre]; linarith) hne
      intro ρ hρ hρre hρs
      have h1 := Complex.abs_re_le_norm (ρ - ((σ₁ : ℂ) + t * I))
      have h2 := Complex.abs_im_le_norm (ρ - ((σ₁ : ℂ) + t * I))
      rw [Complex.sub_re, hre] at h1
      rw [Complex.sub_im, him] at h2
      have h3 : |ρ.im| ≤ T + 3 := by
        have : |ρ.im| ≤ |ρ.im - t| + |t| := by
          have := abs_add_le (ρ.im - t) t
          simpa using this
        linarith
      have h4 := hgapre ρ hρ hρre h3
      rw [abs_sub_comm] at h4
      linarith
    · have := one_div_le_one_div_of_le (by positivity : 0 < 3 * κ / 4) hnorm
      rwa [one_div_div] at this

  have hBH : ∀ v : ℝ, |v| = T' → ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ N + 1 := by
    intro v hv x hx hx'
    have hre : ((x : ℂ) + v * I).re = x := by simp
    have him : ((x : ℂ) + v * I).im = v := by simp
    have hnorm : 1 ≤ ‖(x : ℂ) + v * I - 1‖ := by
      have h1 := Complex.abs_im_le_norm ((x : ℂ) + v * I - 1)
      have h2 : ((x : ℂ) + v * I - 1).im = v := by simp
      rw [h2, hv] at h1
      linarith
    have hne : (x : ℂ) + v * I ≠ 1 := by
      intro h
      rw [h] at hnorm
      simp at hnorm
      linarith
    apply exm_neg hC₂ χ T δ _ _ hM hT hδ0 (by rw [him, hv]; linarith) _ (by norm_num)
    · apply hneg M χ _ δ hM hδ0 hδ' (by rw [hre]; linarith) (by rw [hre]; linarith) hne
      intro ρ hρ hρre _
      have h2 := Complex.abs_im_le_norm (ρ - ((x : ℂ) + v * I))
      rw [Complex.sub_im, him] at h2
      have h4 := hgapim ρ hρ hρre
      rw [← hv] at h4
      have h5 := abs_abs_sub_abs_le ρ.im v
      linarith
    · have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnorm
      simpa using this
  have hH : ∀ v : ℝ, |v| = T' → ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤
      3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2 := by
    intro v hv
    have h := ex_horiz_bound χ y σ₁ σ₀ v (N + 1) (by linarith) (by linarith) (by rw [hv]; linarith)
      (by linarith) (hBH v hv)
    have hv2 : v ^ 2 = T' ^ 2 := by rw [← hv, sq_abs]
    rw [hv2, hyσ₀] at h
    refine h.trans ?_
    have : σ₀ - σ₁ ≤ 3 := by linarith
    gcongr
  have hLf := ex_left_bound χ y σ₁ T' (N + 4 / (3 * κ)) (by linarith) (by linarith) hσ1 hT'0.le hBL
  have hTl := htail M χ y σ₀ T' (by linarith) hσ₀1 (by linarith)
  have hinv : 1 / (σ₀ - 1) = Real.log y := by rw [hσ₀]; simp
  rw [hinv, hyσ₀] at hTl
  have hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T' := by
    intro w hw1 _ hw3 hw0
    have h1 := hgapre w hw0 (by linarith) (by linarith)
    have h2 := hgapim w hw0 (by linarith)
    constructor
    · rcases hw1.lt_or_eq with h | h
      · exact h
      · rw [h] at h1; simp at h1; linarith
    · rcases hw3.lt_or_eq with h | h
      · exact h
      · rw [h] at h2; simp at h2; linarith
  have hrect := ex_rect_Fchi χ y hy0 σ₁ σ₀ T' (by linarith) hσ1 hσ₀1 hT'0 Z hZ hedge
  have hper := (perron_formula_character M χ y (by linarith) σ₀ hσ₀1).2
  unfold Formalism.ZF.rectInt at hrect
  have halg := exm_alg _ _ _ _ _ _ _ _ _ y hy0 hper hrect
  have hD : (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) / (y : ℂ) =
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) := by
    split_ifs
    · push_cast; field_simp
    · simp
  have hS : (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) / (y : ℂ) =
      ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [exKer, Complex.cpow_sub _ _ hyC, Complex.cpow_one]
    ring
  rw [hD, hS] at halg
  rw [halg]
  exact exm_norm _ _ _ _ _ y _ _ _ _ hy0 hTl hLf (hH (-T') (by rw [abs_neg, abs_of_pos hT'0]))
    (hH T' (abs_of_pos hT'0))

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end
end
