module

public import Formalism.UnipotentAdelicQuotients.EllReg
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.BaseLevel
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.ConvolutionBound
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.Decompose
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.ExistsSmoothExt
public import Formalism.UnipotentAdelicQuotients.EllRegCut
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.PairingFourier
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.StepCore
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.SymbLower
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeakFourier
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeightDiff
public import Formalism.UnipotentAdelicQuotients.EllipticRegularity.WeightedNormFinite
public import Formalism.UnipotentAdelicQuotients.EllRegStep

-- Source module: Formalism.UnipotentAdelicQuotients.EllipticRegularity.IteratedPartialFourierChar

section

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

noncomputable def eL {d : ℕ} (ξ : E d) : E d →L[ℝ] ℂ :=
  (-(2 * (Real.pi : ℂ) * Complex.I)) • (Complex.ofRealCLM.comp (innerSL ℝ ξ))

lemma eF_eq_exp {d : ℕ} (ξ : E d) : eF ξ = fun y => Complex.exp (eL ξ y) := by
  funext y
  simp only [eF, eL, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, real_inner_comm y ξ]
  ring_nf

lemma hasFDerivAt_eF {d : ℕ} (ξ y : E d) :
    HasFDerivAt (eF ξ) (Complex.exp (eL ξ y) • eL ξ) y := by
  rw [eF_eq_exp]
  exact (eL ξ).hasFDerivAt.cexp

lemma eL_ev {d : ℕ} (ξ : E d) (j : Fin d) : eL ξ (ev j) = -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)) := by
  simp only [eL, ev, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, Complex.ofRealCLM_apply, smul_eq_mul, EuclideanSpace.inner_single_right]
  simp

theorem iteratedPartialFourierChar : DwExp := by
  intro d ξ w
  induction w with
  | nil => funext y; simp [dw]
  | cons j w ih =>
    funext x
    have hfun : dw w (eF ξ) =
        fun y => (w.map fun j => -(2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ))).prod * eF ξ y := ih
    show fderiv ℝ (dw w (eF ξ)) x (ev j) = _
    rw [hfun, ((hasFDerivAt_eF ξ x).const_mul _).fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, eL_ev, List.map_cons, List.prod_cons,
      eF_eq_exp]
    ring

end ZetaZeros.D.EllReg
end
end

-- Source module: Formalism.UnipotentAdelicQuotients.EllipticRegularity.Moments

section

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

theorem moments_integrable_of_nrm {d : ℕ} (F : E d → ℂ) (hF : Continuous F)
    (h : ∀ s : ℕ, nrm (s : ℝ) 0 0 F < ⊤) (n : ℕ) :
    Integrable (fun v : E d => ‖v‖ ^ n * ‖F v‖) := by
  set m : ℕ := n + (d + 1) with hm
  let A : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ m * ‖F v‖ ^ 2
  let B : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)
  have hAm : Continuous A := by
    have : Continuous fun v : E d => (1 + ‖v‖ ^ 2) := by fun_prop
    exact (this.pow m).mul ((continuous_norm.comp hF).pow 2)
  have hA : Integrable A := by
    refine ⟨hAm.aestronglyMeasurable, ?_⟩
    have hs := h m
    unfold nrm om at hs
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (lintegral_mono fun v => le_of_eq ?_) hs
    have ht0 : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by positivity
    rw [Real.enorm_eq_ofReal (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [A]
    congr 1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, zero_div, neg_zero,
      Real.rpow_zero, mul_one]
    rw [← Real.rpow_natCast ((1 + ‖v‖ ^ 2) ^ ((m : ℝ) / 2)), ← Real.rpow_mul ht0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hB : Integrable B := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [finrank_euclideanSpace_fin]
    linarith
  refine (hA.add hB).mono' ((continuous_norm.pow n).mul (continuous_norm.comp hF)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  have ht1 : (1 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have ht0 : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by linarith
  have hBv : B v = ((1 + ‖v‖ ^ 2) ^ (d + 1))⁻¹ := by
    simp only [B]
    rw [show -(2 * ((d : ℝ) + 1)) / 2 = -(((d + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg ht0.le,
      Real.rpow_natCast]
  have hAB : A v * B v = (1 + ‖v‖ ^ 2) ^ n * ‖F v‖ ^ 2 := by
    rw [hBv]
    simp only [A, hm, pow_add]
    field_simp
  have hx : (‖v‖ ^ n * ‖F v‖) ^ 2 ≤ A v * B v := by
    rw [hAB, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    gcongr
    linarith
  have hA0 : 0 ≤ A v := by positivity
  have hB0 : 0 ≤ B v := by simp only [B]; positivity
  have hx0 : 0 ≤ ‖v‖ ^ n * ‖F v‖ := by positivity
  rw [Real.norm_of_nonneg hx0]
  show ‖v‖ ^ n * ‖F v‖ ≤ A v + B v
  nlinarith [sq_nonneg (A v - B v), mul_nonneg hA0 hB0]

theorem smoothOfSobolevAll : MomentsSmooth := by
  intro d g hg hgc hs
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hFc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ (E d)) Real.continuous_fourierChar
      (by simpa using continuous_inner) hgi
  have hmom := moments_integrable_of_nrm (𝓕 g) hFc hs
  have hFi : Integrable (𝓕 g) := by
    have h0 := hmom 0
    simp only [pow_zero, one_mul] at h0
    exact (integrable_norm_iff hFc.aestronglyMeasurable).mp h0
  have hinv := hg.fourierInv_fourier_eq hgi hFi
  have hsm : ContDiff ℝ ∞ (𝓕 (𝓕 g)) :=
    VectorFourier.contDiff_fourierIntegral (L := innerSL ℝ) (μ := volume) (N := ⊤) (f := 𝓕 g)
      (fun n _ => hmom n)
  have hg' : g = fun w => 𝓕 (𝓕 g) (-w) := by
    conv_lhs => rw [← hinv]
    ext w
    exact Real.fourierInv_eq_fourier_neg _ w
  rw [hg']
  exact hsm.comp contDiff_neg

end ZetaZeros.D.EllReg
end
end

-- Source module: Formalism.UnipotentAdelicQuotients.EllipticRegularity.PairingLocal

section

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma dw_eventuallyEq {d : ℕ} (w : List (Fin d)) {f f' : E d → ℂ} {y : E d} (h : f =ᶠ[𝓝 y] f') :
    dw w f =ᶠ[𝓝 y] dw w f' := by
  induction w with
  | nil => simpa [dw] using h
  | cons j w ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with x hx
    show fderiv ℝ (dw w f) x (ev j) = fderiv ℝ (dw w f') x (ev j)
    rw [hx]

theorem adjointPairingLocal : PairingLocal := by
  intro d m b b' g φ V hV hg hb
  congr 1
  funext y
  by_cases hy : y ∈ V
  · congr 1
    unfold trOp
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
    congr 1

    have hev : (fun y => b n w y * φ y) =ᶠ[𝓝 y] (fun y => b' n w y * φ y) := by
      filter_upwards [hV.mem_nhds hy] with z hz
      rw [hb n w z hz]
    exact (dw_eventuallyEq _ hev).eq_of_nhds
  · have hg0 : g y = 0 := by
      first
        | exact image_eq_zero_of_nmem_tsupport (fun h => hy (hg h))
        | exact image_eq_zero_of_notMem_tsupport (fun h => hy (hg h))
    rw [hg0, zero_mul, zero_mul]

end ZetaZeros.D.EllReg
end
end

-- Source module: Formalism.UnipotentAdelicQuotients.EllipticRegularity.SmoothOfLocallySmooth

section

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

theorem integralFourierChar : FourierPair := by
  intro d g _ _ ξ
  rw [Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show g y * eF ξ y = Complex.exp (((-2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) • g y
  rw [smul_eq_mul, mul_comm (Complex.exp _)]
  congr 1
  simp only [eF]
  congr 1
  push_cast
  ring

theorem existsBump : Bump := by
  intro d x0 r hr
  let f : ContDiffBump x0 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, ?_⟩
  · rw [f.tsupport_eq]
    exact closedBall_subset_ball (show r / 2 < r by linarith)
  · filter_upwards [ball_mem_nhds x0 (show (0 : ℝ) < r / 4 by positivity)] with y hy
    exact f.one_of_mem_closedBall (ball_subset_closedBall hy)

theorem cutoffContinuous : CutCont := by
  intro d U u χ hU hu hχs hχc hχt
  have hχ' : Continuous (fun x => (χ x : ℂ)) := Complex.continuous_ofReal.comp hχs.continuous
  have hsub : tsupport (cut χ u) ⊆ tsupport χ := by
    apply closure_mono
    intro x hx
    by_contra h0
    apply hx
    have h0' : χ x = 0 := by simpa using h0
    simp [cut, h0']
  have hcont : ContinuousOn (cut χ u) U := hχ'.continuousOn.mul hu
  exact ⟨hcont.continuous_of_tsupport_subset hU (hsub.trans hχt),
    IsCompact.of_isClosed_subset hχc (isClosed_tsupport _) hsub⟩

theorem smoothOfLocallySmooth : LocalGlobal := by
  intro d U f _ h x hx
  obtain ⟨χ, hχ1, hχf⟩ := h x hx
  have heq : cut χ f =ᶠ[𝓝 x] f := by
    filter_upwards [hχ1] with y hy
    simp [cut, hy]
  exact (hχf.contDiffAt.congr_of_eventuallyEq heq.symm).contDiffWithinAt

end ZetaZeros.D.EllReg
end
end

-- Source module: Formalism.UnipotentAdelicQuotients.EllRegCheck

section

@[expose] public section

namespace ZetaZeros.D.EllReg

theorem elliptic_regularity_of_parts : Internal := by
  have hSP : StepOfParts :=
    stepOfParts_of frozenDecompositionOfParts weightedNormFinite weightedNormLimit regularity_inductive_step
  exact internal_of_all smoothOfSobolevAll existsBump cutoffContinuous smoothOfLocallySmooth
    sobolevOfCompactSupport symbolLowerBound sobolevWeightLipschitz convolution_bound frozenKernelSmall
    adjointPairingFourier iteratedPartialFourierChar integralFourierChar adjointPairingLocal weakEquationFourier hSP

end ZetaZeros.D.EllReg
end
end
