module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityExistsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedDerivativeSystemSmoothStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuous
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixExpCurveDerivativeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationAeEqConvolutionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationDifferentiableStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationEvaluationContinuousStatement
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularRepresentationContinuousStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateDerivativeIntegralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSequenceUniformCauchyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivativesStatement
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2LimitEqPointwiseLimitHolds

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem l2_limit_eq_pointwise_limit : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (a : ℕ → Mat n → V) (b : Mat n → V) (x : Lp V 2 μ), (∀ k, MemLp (fun y : G n => a k y.val) 2 μ) → Tendsto (fun k => cls μ (a k)) atTop (𝓝 x) → (∀ z ∈ GLs n, Tendsto (fun k => a k z) atTop (𝓝 (b z))) → MemLp (fun y : G n => b y.val) 2 μ ∧ cls μ b = x := by
  intro n _ _ μ _ V _ _ _ a b x hm hc hp
  have hin : TendstoInMeasure μ (fun k => (cls μ (a k) : G n → V)) atTop (x : G n → V) :=
    tendstoInMeasure_of_tendsto_Lp hc
  obtain ⟨ns, hns, hae⟩ := hin.exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂μ, ∀ k, (cls μ (a k) : G n → V) y = a k y.val :=
    ae_all_iff.2 fun k => coe_cls μ (hm k)
  have hbx : (fun y : G n => b y.val) =ᵐ[μ] x := by
    filter_upwards [hae, hall] with y h1 h2
    have hy : y.val ∈ GLs n := by
      have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
      exact hu.ne_zero
    have h3 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (b y.val)) :=
      (hp y.val hy).comp hns.tendsto_atTop
    have h4 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (x y)) := by
      simpa only [h2] using h1
    exact tendsto_nhds_unique h3 h4
  exact cls_of_ae μ hbx

end GlobalTheory.CompanionTheory.PresSobA
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2LimitEqPointwiseLimitHoldsStatement

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.l2_limit_eq_pointwise_limit_holds : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (a : ℕ → Mat n → V) (b : Mat n → V) (x : Lp V 2 μ), (∀ k, MemLp (fun y : G n => a k y.val) 2 μ) → Tendsto (fun k => cls μ (a k)) atTop (𝓝 x) → (∀ z ∈ GLs n, Tendsto (fun k => a k z) atTop (𝓝 (b z))) → MemLp (fun y : G n => b y.val) 2 μ ∧ cls μ b = x := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit | exact GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit | (intros; apply GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftConvolutionApproximation

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem norm_lConv_sub_le : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → (∀ y, 0 ≤ φ y) → (∫ y : G n, φ y.val ∂μ = 1) → ∀ (x : Lp V 2 μ) (ε : ℝ), (∀ y : G n, φ y.val ≠ 0 → ‖lT μ V y x - x‖ ≤ ε) → ‖lConv μ V φ x - x‖ ≤ ε := by
  intro n _ _ μ _ V _ _ _ hU φ hφ hpos h1 x ε hε
  have hemb := GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n
  have hφc : Continuous fun y : G n => φ y.val := hφ.1.continuous.comp hemb.continuous
  have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine (hemb.isInducing.isCompact_preimage_iff ?_).2 hφ.2.1
    intro z hz
    have hdet : z.det ≠ 0 := hφ.2.2 hz
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det z).2 (isUnit_iff_ne_zero.2 hdet)
    exact ⟨u, rfl⟩
  have hcs : HasCompactSupport (fun y : G n => φ y.val) :=
    HasCompactSupport.of_support_subset_isCompact hK (fun y hy => subset_tsupport φ hy)
  have hL := (translations_strongly_continuous n μ V hU x).2
  have hint1 : Integrable (fun y : G n => φ y.val) μ := hφc.integrable_of_hasCompactSupport hcs
  have hf : Integrable (fun y : G n => φ y.val • lT μ V y x) μ :=
    (hφc.smul hL).integrable_of_hasCompactSupport hcs.smul_right
  have hg : Integrable (fun y : G n => φ y.val • x) μ := hint1.smul_const x
  have e : lConv μ V φ x - x = ∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hf hg, integral_smul_const, h1, one_smul]
    rfl
  rw [e]
  calc ‖∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ‖ ≤ ∫ y : G n, φ y.val * ε ∂μ := by
        refine norm_integral_le_of_norm_le (hint1.mul_const ε) (ae_of_all _ fun y => ?_)
        by_cases h0 : φ y.val = 0
        · simp [h0]
        · rw [norm_smul, Real.norm_of_nonneg (hpos _)]
          exact mul_le_mul_of_nonneg_left (hε y h0) (hpos _)
    _ = ε := by rw [integral_mul_const, h1, one_mul]

end GlobalTheory.CompanionTheory.PresSobA
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftConvolutionApproximationStatement

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.left_convolution_approximation : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → (∀ y, 0 ≤ φ y) → (∫ y : G n, φ y.val ∂μ = 1) → ∀ (x : Lp V 2 μ) (ε : ℝ), (∀ y : G n, φ y.val ≠ 0 → ‖lT μ V y x - x‖ ≤ ε) → ‖lConv μ V φ x - x‖ ≤ ε := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le | exact GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le | (intros; apply GlobalTheory.CompanionTheory.PresSobA.norm_lConv_sub_le <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationRightTranslate

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem Mol_rR_eq (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (hU : Unimod) (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n) :
    Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have he : MeasurableEmbedding (fun y : G n => y * h) := (Homeomorph.mulRight h).measurableEmbedding
  have h1 : Mol μ φ (⇑(rR μ V h x)) z = ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x (u * h) ∂μ := by
    unfold Mol
    refine integral_congr_ae ?_
    filter_upwards [rR_coe μ hU h x] with u hu
    rw [hu]
  rw [h1]
  unfold Mol
  rw [← hm.integral_comp he (fun u : G n => φ (z * h.val * (u⁻¹ : G n).val) • x u)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have : z * h.val * ((u * h)⁻¹ : G n).val = z * (u⁻¹ : G n).val := by
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.one_mul]
  simp only [this]

end GlobalTheory.CompanionTheory.PresSobA
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationRightTranslateStatement

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.mollification_right_translate : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n), Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq | exact GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq | (intros; apply GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq <;> assumption)
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreserved

section

@[expose] public section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem rR_one (hU : Unimod) (y : Lp V 2 μ) : rR μ V 1 y = y := by
  apply Lp.ext
  filter_upwards [rR_coe μ hU 1 y] with z hz
  simpa using hz

theorem lT_one (y : Lp V 2 μ) : lT μ V 1 y = y := by
  apply Lp.ext
  filter_upwards [lT_coe μ 1 y] with z hz
  simpa using hz

theorem orbit_deriv (hU : Unimod) {f : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (h0 : MemLp (fun y : G n => f y.val) 2 μ) (h1 : MemLp (fun y : G n => Rd X f y.val) 2 μ) :
    HasDerivAt (fun t : ℝ => rR μ V (expC X t) (cls μ f)) (cls μ (Rd X f)) 0 := by
  have hc : Continuous (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f))) :=
    (GlobalTheory.T.regular_representation_continuous n μ V hU _).1.comp (GlobalTheory.T.matrix_exp_curve_derivative n X).1
  have hd := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := 0)
    (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simp only [expC_zero, rR_one hU] at hd
  have he : (fun t : ℝ => rR μ V (expC X t) (cls μ f)) =
      fun t : ℝ => (∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f))) + cls μ f := by
    funext t
    rw [← GlobalTheory.T.right_translate_derivative_integral n μ V hU f X hf h0 h1 t]
    abel
  rw [he]
  exact hd.add_const _

theorem mol_family (hU : Unimod) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ)
    (hx : ∀ w p, HasDerivAt (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) (x (p :: w)) 0)
    {φ : Mat n → ℝ} (hφ : IsTest φ) :
    (∀ w, ContDiffOn ℝ ∞ (Mol μ φ (⇑(x w))) (GLs n)) ∧
      ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Mol μ φ (⇑(x w))) z = Mol μ φ (⇑(x (p :: w))) z := by
  have hd : ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Mol μ φ (⇑(x w))) z = Mol μ φ (⇑(x (p :: w))) z := by
    intro w p z hz
    obtain ⟨Lz, hL⟩ := GlobalTheory.T.mollification_evaluation_continuous n μ V hU φ hφ z hz
    have h1 : HasDerivAt (fun t : ℝ => Lz (rR μ V (expC (bs p) t) (x w))) (Lz (x (p :: w))) 0 :=
      Lz.hasFDerivAt.comp_hasDerivAt 0 (hx w p)
    have hcur : HasDerivAt (fun t : ℝ => z * (expC (bs p) t).val) (z * bs p) 0 := by
      have h0 := (GlobalTheory.T.matrix_exp_curve_derivative n (bs p)).2 0
      rw [expC_zero] at h0
      simp only [Units.val_one, one_mul] at h0
      exact (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ z) : Mat n →L[ℝ] Mat n).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
    have hdiff := (GlobalTheory.T.mollification_differentiable n μ V hU φ hφ (x w) z hz).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => Mol μ φ (⇑(x w)) (z * (expC (bs p) t).val))
        (fderiv ℝ (Mol μ φ (⇑(x w))) z (z * bs p)) 0 := by
      have hz0 : z * (expC (bs p) 0).val = z := by simp [expC_zero]
      have hdiff' : HasFDerivAt (Mol μ φ (⇑(x w))) (fderiv ℝ (Mol μ φ (⇑(x w))) z)
          (z * (expC (bs p) 0).val) := by rw [hz0]; exact hdiff
      exact hdiff'.comp_hasDerivAt 0 hcur
    have h3 : (fun t : ℝ => Lz (rR μ V (expC (bs p) t) (x w))) =
        fun t : ℝ => Mol μ φ (⇑(x w)) (z * (expC (bs p) t).val) := by
      funext t
      rw [hL, GlobalTheory.T.mollification_right_translate n μ V hU]
    rw [h3] at h1
    rw [← hL]
    exact h2.unique h1
  refine ⟨fun w => ?_, hd⟩
  exact GlobalTheory.T.closed_derivative_system_smooth n V (List (Bool × Fin n × Fin n)) (fun w => Mol μ φ (⇑(x w))) (fun p w => p :: w)
    (fun w z hz => GlobalTheory.T.mollification_differentiable n μ V hU φ hφ (x w) z hz) (fun w p z hz => hd w p z hz) w

theorem limit_sob (hS : SobG) (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ)
    (hg : ∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) (hm : ∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ)
    (hx : ∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) :
    ∃ f', Sob μ f' ∧ ∀ w, cls μ (Rw w f') = x w := by
  obtain ⟨Gf, hu, hc, hw⟩ := GlobalTheory.T.uniform_limit_right_derivatives n V g hg (GlobalTheory.T.sobolev_sequence_uniform_cauchy hS n μ V g x hg hm hx)
  have key : ∀ w, MemLp (fun y : G n => Rw w (Gf []) y.val) 2 μ ∧ cls μ (Rw w (Gf [])) = x w := by
    intro w
    refine GlobalTheory.T.l2_limit_eq_pointwise_limit_holds n μ V (fun k => Rw w (g k)) (Rw w (Gf [])) (x w) (fun k => hm k w) (hx w) ?_
    intro z hz
    rw [hw w z hz]
    exact (hu w).tendsto_at hz
  exact ⟨Gf [], ⟨hc, fun w => (key w).1⟩, fun w => (key w).2⟩

end GlobalTheory.CompanionTheory.PresSobA


open GlobalTheory.CompanionTheory.PresSobA in
theorem GlobalTheory.CompanionTheory.PresSobA.presSob : PresSob := by
  intro n _ _ μ _ V _ _ _ S hLg hU hRC hS hcomm f hf
  have hsob : ∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n) := fun w => GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' hf.1 w
  set x : List (Bool × Fin n × Fin n) → Lp V 2 μ := fun w => S (cls μ (Rw w f)) with hxdef
  have hx : ∀ w p, HasDerivAt (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) (x (p :: w)) 0 := by
    intro w p
    have h1 := orbit_deriv (μ := μ) hU (bs p) (hsob w) (hf.2 w) (hf.2 (p :: w))
    have h2 : HasDerivAt (fun t : ℝ => (S.restrictScalars ℝ) (rR μ V (expC (bs p) t) (cls μ (Rw w f))))
        ((S.restrictScalars ℝ) (cls μ (Rd (bs p) (Rw w f)))) 0 :=
      (S.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
    have h3 : (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) =
        fun t : ℝ => (S.restrictScalars ℝ) (rR μ V (expC (bs p) t) (cls μ (Rw w f))) := by
      funext t
      exact (DFunLike.congr_fun (hcomm (expC (bs p) t)) _).symm
    rw [h3]
    exact h2
  obtain ⟨φ, hφ, hφ0, hφ1, hφs⟩ := GlobalTheory.T.approximate_identity_exists n μ
  have hfam := fun k => mol_family (μ := μ) hU x hx (hφ k)
  have hRw : ∀ k w, ∀ z ∈ GLs n, Rw w (Mol μ (φ k) (⇑(x []))) z = Mol μ (φ k) (⇑(x w)) z := by
    intro k w
    induction w with
    | nil => exact fun z _ => rfl
    | cons p w ih =>
      intro z hz
      exact (Rd_congr ih (bs p) z hz).trans ((hfam k).2 w p z hz)
  have hae : ∀ k w, (fun y : G n => Rw w (Mol μ (φ k) (⇑(x []))) y.val) =ᵐ[μ] lConv μ V (φ k) (x w) := by
    intro k w
    have h0 : (fun y : G n => Rw w (Mol μ (φ k) (⇑(x []))) y.val) = fun y : G n => Mol μ (φ k) (⇑(x w)) y.val :=
      funext fun y => hRw k w y.val (by
        have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
        exact this.ne_zero)
    rw [h0]
    exact GlobalTheory.T.mollification_ae_eq_convolution n μ V hU (φ k) (hφ k) (x w)
  have hlim : ∀ w, Tendsto (fun k => cls μ (Rw w (Mol μ (φ k) (⇑(x []))))) atTop (𝓝 (x w)) := by
    intro w
    have : (fun k => cls μ (Rw w (Mol μ (φ k) (⇑(x []))))) = fun k => lConv μ V (φ k) (x w) :=
      funext fun k => (cls_of_ae μ (hae k w)).2
    rw [this, Metric.tendsto_nhds]
    intro ε hε
    have hc : Continuous (fun y : G n => lT μ V y (x w)) := (GlobalTheory.T.regular_representation_continuous n μ V hU _).2
    have h1 : {y : G n | dist (lT μ V y (x w)) (x w) < ε / 2} ∈ 𝓝 (1 : G n) := by
      have h2 := (hc.tendsto (1 : G n))
      rw [lT_one] at h2
      exact h2 (Metric.ball_mem_nhds _ (half_pos hε))
    filter_upwards [hφs _ h1] with k hk
    have h3 := GlobalTheory.T.left_convolution_approximation n μ V hU (φ k) (hφ k) (hφ0 k) (hφ1 k) (x w) (ε / 2)
      (fun y hy => by
        have h4 := hk y hy
        rw [dist_eq_norm] at h4
        exact h4.le)
    rw [dist_eq_norm]
    linarith
  obtain ⟨f', hf', hcl⟩ := limit_sob (μ := μ) hS (fun k => Mol μ (φ k) (⇑(x []))) x (fun k => (hfam k).1 [])
    (fun k w => (cls_of_ae μ (hae k w)).1) hlim
  exact ⟨f', hf', hcl [], hcl⟩
end
end
end
