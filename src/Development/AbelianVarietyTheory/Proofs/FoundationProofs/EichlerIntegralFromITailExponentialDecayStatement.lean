module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnVerticalRayNormIntegralLeStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CauchyParallelogramUpperHalfPlane

section

@[expose] public section

open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem cauchy_parallelogram_upper_half_plane :
    ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  intro g τ S hg hτ hS
  set φ : ℝ × ℝ → ℂ := fun x => Complex.I + (x.1 : ℂ) * (τ - Complex.I) + (x.2 : ℂ) * Complex.I
    with hφdef
  set L : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (τ - Complex.I) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I with hLdef
  have hφL : φ = fun x => Complex.I + L x := by
    funext x; simp [φ, L, Complex.real_smul]; ring
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ x : ℝ × ℝ, 0 ≤ x.1 → x.1 ≤ 1 → 0 ≤ x.2 → 0 < (φ x).im := by
    rintro ⟨t, s⟩ h0 h1 h2
    simp only [φ, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    rcases h1.lt_or_eq with h | h
    · nlinarith [mul_nonneg h0 hτ.le]
    · subst h; simp at *; nlinarith
  have hφc : Continuous φ := by
    rw [hφL]; exact continuous_const.add L.continuous
  have hcont : ContinuousOn (fun x => g (φ x)) (uIcc (0:ℝ) 1 ×ˢ uIcc (0:ℝ) S) := by
    refine hg.continuousOn.comp hφc.continuousOn ?_
    intro x hx
    rw [uIcc_of_le zero_le_one, uIcc_of_le hS] at hx
    exact hpos x hx.1.1 hx.1.2 hx.2.1
  set F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun x =>
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv g (φ x))).restrictScalars ℝ).comp L
  have hder : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) ×ˢ Ioo (min (0:ℝ) S) (max (0:ℝ) S),
      HasFDerivAt (fun x => g (φ x)) (F' x) x := by
    intro x hx
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one, min_eq_left hS, max_eq_right hS] at hx
    have hz : 0 < (φ x).im := hpos x hx.1.1.le hx.1.2.le hx.2.1.le
    have hgd : HasDerivAt g (deriv g (φ x)) (φ x) :=
      (hg.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hφd : HasFDerivAt φ L x := by
      rw [hφL]; exact L.hasFDerivAt.const_add _
    exact (hgd.hasFDerivAt.restrictScalars ℝ).comp x hφd
  have key := integral2_divergence_prod_of_hasFDerivAt
    (fun x => Complex.I * g (φ x)) (fun x => -(τ - Complex.I) * g (φ x))
    (fun x => Complex.I • F' x) (fun x => (-(τ - Complex.I)) • F' x) 0 0 1 S
    (continuousOn_const.mul hcont) (continuousOn_const.mul hcont)
    (fun x hx => (hder x hx).const_mul _) (fun x hx => (hder x hx).const_mul _)
    (by
      have : (fun x : ℝ × ℝ => (Complex.I • F' x) (1, 0) + ((-(τ - Complex.I)) • F' x) (0, 1))
          = fun _ => 0 := by
        funext x; simp [F', L]; ring
      rw [this]; exact integrableOn_zero)
  have hzero : ∀ x : ℝ × ℝ, (Complex.I • F' x) (1, 0) + ((-(τ - Complex.I)) • F' x) (0, 1) = 0 := by
    intro x; simp [F', L]; ring
  simp only [hzero, intervalIntegral.integral_zero, intervalIntegral.integral_const_mul] at key
  have e1 : ∀ s : ℝ, φ (1, s) = τ + s * Complex.I := by
    intro s; simp only [φ]; push_cast; ring
  have e0 : ∀ s : ℝ, φ (0, s) = Complex.I + s * Complex.I := by
    intro s; simp only [φ]; push_cast; ring
  have eS : ∀ t : ℝ, φ (t, S) = Complex.I + t * (τ - Complex.I) + S * Complex.I := fun _ => rfl
  have eT : ∀ t : ℝ, φ (t, 0) = Complex.I + t * (τ - Complex.I) := by
    intro t; simp only [φ]; push_cast; ring
  simp only [e1, e0, eS, eT] at key
  linear_combination -key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CauchyParallelogramUpperHalfPlaneStatement

section

@[expose] public section

open MeasureTheory Filter Topology Set

theorem _root_.GlobalTheory.T.integral_segment_eq_parallelogram_sides : ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  first | exact @GlobalTheory.cauchy_parallelogram_upper_half_plane | exact GlobalTheory.cauchy_parallelogram_upper_half_plane | (intros; apply GlobalTheory.cauchy_parallelogram_upper_half_plane <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TopSideIntegralTendstoZero

section

@[expose] public section

open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem top_side_integral_tendsto_zero : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    Tendsto (fun S : ℝ => ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop (𝓝 0) := by
  intro g K c m τ _ hc hg hτ
  set B : ℝ := 2 + ‖τ - Complex.I‖ with hB
  have hB0 : 0 ≤ B := by positivity
  set F : ℝ → ℝ := fun S => |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m with hF
  have hpt : ∀ S : ℝ, 0 ≤ S → ∀ t ∈ Set.uIoc (0:ℝ) 1,
      ‖g (Complex.I + t * (τ - Complex.I) + S * Complex.I)‖ ≤ F S := by
    intro S hS t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    set z := Complex.I + t * (τ - Complex.I) + S * Complex.I with hz
    have him : z.im = 1 + t * (τ.im - 1) + S := by
      simp [hz]
    have him1 : 1 + S ≤ z.im := by
      rw [him]; nlinarith
    have hnorm : 1 + ‖z‖ ≤ B + S := by
      have h1 : ‖z‖ ≤ ‖Complex.I‖ + ‖(t:ℂ) * (τ - Complex.I)‖ + ‖(S:ℂ) * Complex.I‖ := by
        rw [hz]; exact norm_add₃_le
      have h2 : ‖(t:ℂ) * (τ - Complex.I)‖ ≤ ‖τ - Complex.I‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        exact mul_le_of_le_one_left (norm_nonneg _) ht1
      have h3 : ‖(S:ℂ) * Complex.I‖ = S := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
      rw [Complex.norm_I] at h1
      rw [hB]; linarith
    have he : Real.exp (-c * z.im) ≤ Real.exp (-c * (1 + S)) := Real.exp_le_exp.mpr (by nlinarith)
    have hp : (1 + ‖z‖) ^ m ≤ (B + S) ^ m := pow_le_pow_left₀ (by positivity) hnorm m
    calc ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m := hg z (by linarith)
      _ ≤ |K| * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m := by
          gcongr; exact le_abs_self K
      _ ≤ |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m :=
          mul_le_mul (mul_le_mul_of_nonneg_left he (abs_nonneg K)) hp (by positivity) (by positivity)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun S : ℝ => c * (B + S)) atTop atTop :=
      (tendsto_atTop_add_const_left atTop B tendsto_id).const_mul_atTop hc
    have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp h1).const_mul
      (|K| * (c ^ m)⁻¹ * Real.exp (c * B - c))
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards with S
    have hcm : c ^ m ≠ 0 := pow_ne_zero _ hc.ne'
    have hexp : Real.exp (c * B - c) * Real.exp (-(c * (B + S))) = Real.exp (-c * (1 + S)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [Function.comp, hF]
    rw [mul_pow]
    calc |K| * (c ^ m)⁻¹ * Real.exp (c * B - c) * (c ^ m * (B + S) ^ m * Real.exp (-(c * (B + S))))
        = |K| * (Real.exp (c * B - c) * Real.exp (-(c * (B + S)))) * ((c ^ m)⁻¹ * c ^ m) * (B + S) ^ m := by ring
      _ = |K| * Real.exp (-c * (1 + S)) * (B + S) ^ m := by rw [hexp, inv_mul_cancel₀ hcm, mul_one]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
  have := intervalIntegral.norm_integral_le_of_norm_le_const (hpt S hS)
  rwa [sub_zero, abs_one, mul_one] at this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TopSideIntegralTendstoZeroStatement

section

@[expose] public section

open MeasureTheory Filter Topology Set

theorem _root_.GlobalTheory.T.tendsto_integral_shifted_segment_zero_of_exp_decay : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    Tendsto (fun S : ℝ => ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop (𝓝 0) := by
  first | exact @GlobalTheory.top_side_integral_tendsto_zero | exact GlobalTheory.top_side_integral_tendsto_zero | (intros; apply GlobalTheory.top_side_integral_tendsto_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromITailExponentialDecay

section

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
open MeasureTheory Filter Topology Set

namespace GlobalTheory.HeckeFamilyMatrices

theorem eichler_tail_cauchy (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ) (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.im}) (hc : 0 < c)
    (hb : ∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) (hτ : 1 ≤ τ.im) :
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in Ioi (0:ℝ), g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)) := by
  have hI : (1:ℝ) ≤ Complex.I.im := by simp
  have i1 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le g K c m Complex.I hg.continuousOn hc hb hI).1
  have i2 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le g K c m τ hg.continuousOn hc hb hτ).1
  have t1 := intervalIntegral_tendsto_integral_Ioi 0 i1 tendsto_id
  have t2 := intervalIntegral_tendsto_integral_Ioi 0 i2 tendsto_id
  have t3 := GlobalTheory.T.tendsto_integral_shifted_segment_zero_of_exp_decay g K c m τ hg.continuousOn hc hb hτ
  have hlim : Tendsto (fun S : ℝ => Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I)) atTop
      (𝓝 (Complex.I * (∫ s in Ioi (0:ℝ), g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)) + (τ - Complex.I) * 0)) :=
    ((t1.const_mul _).sub (t2.const_mul _)).add (t3.const_mul _)
  rw [mul_zero, add_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
  filter_upwards [eventually_ge_atTop 0] with S hS
  exact GlobalTheory.T.integral_segment_eq_parallelogram_sides g τ S hg (by linarith) hS

theorem eichler_tail : ∀ (w : ℕ) (F : ℍ → ℂ) (C c : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → 0 < c →
    (∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) →
    ∃ (L : ℂ[X]) (C' : ℝ), ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w,
      ‖(eichler w F τ - L).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
  intro w F C c hF hc hbd
  set G : ℂ → ℂ := F ∘ UpperHalfPlane.ofComplex with hGdef
  have hG : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} := UpperHalfPlane.mdifferentiable_iff.mp hF
  let g : ℕ → ℂ → ℂ := fun j z => G z * (-z) ^ (w - j)
  have hg : ∀ j, DifferentiableOn ℂ (g j) {z : ℂ | 0 < z.im} := fun j =>
    hG.mul ((differentiable_id.neg.pow _).differentiableOn)
  have hgb : ∀ j, ∀ z : ℂ, 1 ≤ z.im → ‖g j z‖ ≤ C * Real.exp (-c * z.im) * (1 + ‖z‖) ^ w := by
    intro j z hz
    have hz0 : 0 < z.im := by linarith
    have h1 : ‖G z‖ ≤ C * Real.exp (-c * z.im) := by
      have := hbd ⟨z, hz0⟩ hz
      simpa [hGdef, Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz0] using this
    have h2 : ‖(-z) ^ (w - j)‖ ≤ (1 + ‖z‖) ^ w := by
      rw [norm_pow, norm_neg]
      calc ‖z‖ ^ (w - j) ≤ (1 + ‖z‖) ^ (w - j) := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ (1 + ‖z‖) ^ w := pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.sub_le _ _)
    calc ‖g j z‖ = ‖G z‖ * ‖(-z) ^ (w - j)‖ := norm_mul _ _
      _ ≤ C * Real.exp (-c * z.im) * (1 + ‖z‖) ^ w :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
  set M : ℝ := ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ w
  set Lp : ℂ[X] := ∑ j ∈ Finset.range (w + 1),
      Polynomial.C ((w.choose j : ℂ) * (Complex.I * ∫ s in Ioi (0:ℝ), g j (Complex.I + s * Complex.I))) * X ^ j
    with hLp
  refine ⟨Lp, 2 ^ w * C * M, ?_⟩
  intro τ hτ j hj
  have hj' : j ∈ Finset.range (w + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  have hc1 : (eichler w F τ).coeff j = (w.choose j : ℂ) * ∫ t in (0 : ℝ)..1,
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I) := by
    rw [eichler, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb; rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd hj' h
  have hc2 : Lp.coeff j = (w.choose j : ℂ) * (Complex.I * ∫ s in Ioi (0:ℝ), g j (Complex.I + s * Complex.I)) := by
    rw [hLp, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb; rw [Polynomial.coeff_C_mul_X_pow, if_neg (Ne.symm hb)]
    · intro h; exact absurd hj' h
  have hint : (∫ t in (0 : ℝ)..1,
      (F ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ (w - j) * ((τ : ℂ) - Complex.I)) =
      ((τ : ℂ) - Complex.I) * ∫ t in (0:ℝ)..1, g j (Complex.I + t * ((τ : ℂ) - Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext t; simp only [g, hGdef]; ring
  have hL5 := eichler_tail_cauchy (g j) C c w (τ : ℂ) (hg j) hc (hgb j) hτ
  have hkey : (eichler w F τ - Lp).coeff j = -((w.choose j : ℂ) * Complex.I * ∫ s in Ioi (0:ℝ), g j ((τ : ℂ) + s * Complex.I)) := by
    rw [Polynomial.coeff_sub, hc1, hc2, hint, hL5]; ring
  rw [hkey, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
  have hb3 := (GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le (g j) C c w (τ : ℂ) (hg j).continuousOn hc (hgb j) hτ).2
  have hch : ‖(w.choose j : ℂ)‖ ≤ 2 ^ w := by
    rw [Complex.norm_natCast]; exact_mod_cast Nat.choose_le_two_pow w j
  have hnn : 0 ≤ C * Real.exp (-c * τ.im) * (1 + ‖(τ:ℂ)‖) ^ w * M := (norm_nonneg _).trans hb3
  calc ‖(w.choose j : ℂ)‖ * ‖∫ s in Ioi (0:ℝ), g j ((τ : ℂ) + s * Complex.I)‖
      ≤ 2 ^ w * (C * Real.exp (-c * τ.im) * (1 + ‖(τ:ℂ)‖) ^ w * M) :=
        mul_le_mul hch hb3 (norm_nonneg _) (by positivity)
    _ = 2 ^ w * C * M * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
        ring

end GlobalTheory.HeckeFamilyMatrices
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromITailExponentialDecayStatement

section

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerIntegralFromI_tail_exponential_decay : ∀ (w : ℕ) (F : ℍ → ℂ) (C c : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → 0 < c → (∀ τ : ℍ, 1 ≤ τ.im → ‖F τ‖ ≤ C * Real.exp (-c * τ.im)) → ∃ (L : ℂ[X]) (C' : ℝ), ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(eichler w F τ - L).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.eichler_tail | exact GlobalTheory.HeckeFamilyMatrices.eichler_tail | (intros; apply GlobalTheory.HeckeFamilyMatrices.eichler_tail <;> assumption)
end
end
