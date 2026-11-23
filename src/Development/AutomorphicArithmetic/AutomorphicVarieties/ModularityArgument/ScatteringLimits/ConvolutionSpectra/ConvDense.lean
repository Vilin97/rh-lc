module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvAdj
public import Mathlib.Analysis.Fourier.LpSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.FourAe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Convolution
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Order
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.FourConv

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.fourConv :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (κ : ℝ → V →L[ℂ] W), Ker κ → ∀ u : L V, ∀ᵐ ξ : ℝ,
      Lp.fourierTransformₗᵢ ℝ W (conv κ u) ξ = symb κ (2 * Real.pi * Complex.I * ξ) (Lp.fourierTransformₗᵢ ℝ V u ξ) := by
  intro V _ _ _ _ W _ _ _ _ κ hk u
  have ki : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  let σ : ℝ → V →L[ℂ] W := fun ξ => symb κ (2 * Real.pi * Complex.I * ξ)
  have hσ : ∀ ξ, σ ξ = 𝓕 (fun t => κ (-t)) ξ := fun ξ => by
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
    congr 2
    push_cast; ring
  have σc : Continuous σ := by
    rw [show σ = _ from funext hσ]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ ki.comp_neg
  have σb : ∀ ξ, ‖σ ξ‖ ≤ ∫ t, ‖κ (-t)‖ := fun ξ => by
    rw [hσ]; exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
  set C := ∫ t, ‖κ (-t)‖
  have hm : ∀ v : L V, MemLp (fun ξ => σ ξ (v ξ)) 2 volume := fun v =>
    (Lp.memLp v).of_le_mul (c := C)
      ((ContinuousLinearMap.id ℂ (V →L[ℂ] W)).aestronglyMeasurable_comp₂ σc.aestronglyMeasurable (Lp.aestronglyMeasurable v))
      (Eventually.of_forall fun ξ => (σ ξ).le_of_opNorm_le (σb ξ) _)
  let T : L V → L W := fun v => (hm v).toLp _
  have Tc : Continuous T := by
    refine (LipschitzWith.of_dist_le' (K := C) fun v v' => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub (T v) (T v'), Lp.coeFn_sub v v', (hm v).coeFn_toLp, (hm v').coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, ← map_sub]
    exact (σ x).le_of_opNorm_le (σb x) _
  have key : Lp.fourierTransformₗᵢ ℝ W (conv κ u) = T (Lp.fourierTransformₗᵢ ℝ V u) := by
    refine DenseRange.induction_on (p := fun u : L V => Lp.fourierTransformₗᵢ ℝ W (conv κ u) = T (Lp.fourierTransformₗᵢ ℝ V u))
      (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := V) (p := 2) (μ := volume) ENNReal.ofNat_ne_top) u
      (isClosed_eq ((Lp.fourierTransformₗᵢ ℝ W).continuous.comp (conv κ).continuous)
        (Tc.comp (Lp.fourierTransformₗᵢ ℝ V).continuous)) fun f => ?_
    set w : L V := SchwartzMap.toLpCLM ℝ V 2 volume f
    have wi : Integrable (w : ℝ → V) := f.integrable.congr (f.coeFn_toLp 2 volume).symm
    have e : (conv κ w : ℝ → W) =ᵐ[volume] convolution (fun t => κ (-t)) w (ContinuousLinearMap.id ℂ (V →L[ℂ] W)) volume := by
      filter_upwards [(convSpec κ hk w).1] with x hx
      rw [hx, convolution_def, ← integral_neg_eq_self]
      simp [sub_eq_add_neg]
    have ci : Integrable (conv κ w : ℝ → W) := (ki.comp_neg.integrable_convolution _ wi).congr e.symm
    refine Lp.ext ?_
    filter_upwards [fourAe _ ci, fourAe _ wi, (hm (Lp.fourierTransformₗᵢ ℝ V w)).coeFn_toLp] with ξ h1 h2 h3
    rw [h1, h3, h2, Real.fourier_congr_ae e, Real.fourier_bilin_convolution_eq _ ki.comp_neg wi, hσ]
    rfl
  rw [key]
  exact (hm _).coeFn_toLp
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvDense

section

@[expose] public section

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

private theorem symb_diff {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (κ : ℝ → V →L[ℂ] V) (hk : Ker κ) : Differentiable ℂ (symb κ) := fun z => by
  have c1 : ∀ w : ℂ, Continuous fun t : ℝ => Complex.exp (w * t) • κ t := fun w =>
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).smul hk.1
  have c2 : Continuous fun t : ℝ => (Complex.exp (z * t) * t) • κ t :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul Complex.continuous_ofReal).smul hk.1
  have c3 : Continuous fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := by
    have := hk.1
    fun_prop
  have s1 : HasCompactSupport fun t : ℝ => Complex.exp (z * t) • κ t := hk.2.mono fun t ht h => ht (by simp [h])
  have s3 : HasCompactSupport fun t : ℝ => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖ := hk.2.mono fun t ht h => ht (by simp [h])
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := fun (w : ℂ) (t : ℝ) => Complex.exp (w * t) • κ t)
    (F' := fun (w : ℂ) (t : ℝ) => (Complex.exp (w * t) * t) • κ t) (bound := fun t => Real.exp ((‖z‖ + 1) * |t|) * |t| * ‖κ t‖)
    (Metric.ball_mem_nhds z one_pos) (Eventually.of_forall fun w => (c1 w).aestronglyMeasurable)
    ((c1 z).integrable_of_hasCompactSupport s1) c2.aestronglyMeasurable
    (Eventually.of_forall fun t w hw => ?_) (c3.integrable_of_hasCompactSupport s3)
    (Eventually.of_forall fun t w _ => ?_)).2.differentiableAt
  · rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    have := norm_sub_norm_le w z
    rw [Metric.mem_ball, dist_eq_norm] at hw
    linarith
  · simpa using (((hasDerivAt_id w).mul_const (t : ℂ)).cexp).smul_const (κ t)

theorem UpperTheory.V.Z.IntegralApplyAeEq.convDense :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (β : ℝ → V →L[ℂ] V), Ker β → IsUnit (symb β 0) → DenseRange (conv β) := by
  intro V _ _ _ _ β hk hu
  obtain ⟨k1, k2, k3⟩ := convAdj β hk
  let D : ℂ → ℂ := fun z => LinearMap.det (symb (sharp β) z : V →ₗ[ℂ] V)
  have hD : Differentiable ℂ D := by
    let b := Module.finBasis ℂ V
    have e : D = fun z => ∑ s : Equiv.Perm (Fin (Module.finrank ℂ V)), ((Equiv.Perm.sign s : ℤ) : ℂ) *
        ∏ i, (b.coord (s i)).toContinuousLinearMap (symb (sharp β) z (b i)) := by
      funext z
      simp only [D]
      rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
      simp [LinearMap.toMatrix_apply]
    rw [e]
    refine Differentiable.fun_sum fun s _ => (differentiable_const _).mul ?_
    intro z
    apply (Finset.analyticAt_fun_prod Finset.univ ?_).differentiableAt
    intro i _
    exact ((ContinuousLinearMap.differentiable _).comp ((symb_diff _ k1).clm_apply (differentiable_const _))).analyticAt z
  have h0 : D 0 ≠ 0 := by
    have : IsUnit (symb (sharp β) 0) := by
      rw [k3, map_zero, neg_zero]; exact hu.star
    exact ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2 (ContinuousLinearMap.isUnit_iff_bijective.1 this))).ne_zero
  let g : ℝ → ℂ := fun ξ => D (2 * Real.pi * Complex.I * ξ)
  have ga : AnalyticOnNhd ℝ g univ := fun ξ _ => by
    have h1 : AnalyticAt ℝ (fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ : ℂ)) ξ :=
      analyticAt_const.mul (Complex.ofRealCLM.analyticAt ξ)
    exact (hD.analyticAt _).restrictScalars.comp h1
  have gz : ∀ᵐ ξ : ℝ, g ξ ≠ 0 := by
    have h1 := ga.preimage_zero_mem_codiscreteWithin (x := 0) (by simpa [g] using h0) trivial isConnected_univ
    have h2 := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ h1
    rw [Measure.restrict_univ] at h2
    exact h2
  have inj : ∀ y : L V, conv (sharp β) y = 0 → y = 0 := fun y hy => by
    rw [← (Lp.fourierTransformₗᵢ ℝ V).map_eq_zero_iff]
    refine Lp.ext ?_
    have h1 := fourConv (sharp β) k1 y
    rw [hy, map_zero] at h1
    filter_upwards [h1, gz, Lp.coeFn_zero V 2 (volume : Measure ℝ)] with ξ a b c
    rw [c] at a ⊢
    have := ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit b))).1
    exact this (a₁ := _) (a₂ := 0) (a.symm.trans (map_zero _).symm)
  have bot : (LinearMap.range (conv β : L V →ₗ[ℂ] L V))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    refine inj y (ext_inner_left ℂ fun x => ?_)
    rw [← k2, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
    exact hy _ ⟨x, rfl⟩
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 (Submodule.topologicalClosure_eq_top_iff.2 bot)
end
end
