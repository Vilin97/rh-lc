module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPartialEqRightWordStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeAsRightWords
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevelStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoincareValueBoundOnCubeStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmoothStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.chart_and_right_words_smooth : ∀ n : ℕ, IsOpen (GLs n) ∧ Continuous (cm (n := n)) ∧ cm (n := n) 0 = 0 ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
      (∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n)) ∧ ∀ L : List (Idx n), ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all | exact GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all | (intros; apply GlobalTheory.CompanionTheory.SobGL.Smooth.smooth_all <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeAsRightWordsStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.derivative_as_right_words : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | exact GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | (intros; apply GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparisonStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.haar_chart_integral_comparison : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)), IsCompact Q → IsCompact S → (∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar | exact GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar | (intros; apply GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivative

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.LeftTr

variable {n : ℕ}

theorem isOpen_gls (n : ℕ) : IsOpen (GLs n) := by
  have h : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage h

def lmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

def rmul (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ x)

theorem lmul_apply (x y : Mat n) : lmul x y = x * y := rfl

theorem mul_mem_gls {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem contDiffOn_along {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem contDiffOn_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_along (isOpen_gls n) hf (rmul X)

theorem contDiffOn_Rw {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (w : List (Idx n)) : ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact contDiffOn_Rd ih (bs p)

theorem Rw_left (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V)
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (x : Mat n) (hx : x ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  have hmaps : Set.MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) :=
    fun y hy => mul_mem_gls hx hy
  refine ⟨hf.comp (lmul x).contDiff.contDiffOn hmaps, fun w => ?_⟩
  induction w with
  | nil => intro y _; rfl
  | cons p w ih =>
    intro y hy
    have hev : Rw w (fun y => f (x * y)) =ᶠ[nhds y] (Rw w f) ∘ (lmul x) :=
      Filter.eventually_of_mem ((isOpen_gls n).mem_nhds hy) ih
    have hd : DifferentiableAt ℝ (Rw w f) (lmul x y) :=
      ((contDiffOn_Rw hf w).contDiffAt ((isOpen_gls n).mem_nhds (mul_mem_gls hx hy))).differentiableAt
        (by simp)
    have hc : HasFDerivAt ((Rw w f) ∘ (lmul x))
        ((fderiv ℝ (Rw w f) (lmul x y)).comp (lmul x)) y :=
      hd.hasFDerivAt.comp y (lmul x).hasFDerivAt
    change fderiv ℝ (Rw w (fun y => f (x * y))) y (y * bs p) =
      fderiv ℝ (Rw w f) (x * y) (x * y * bs p)
    rw [hev.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, lmul_apply, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.SobGL.LeftTr
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateRightDerivativeStatement

section

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.left_translate_right_derivative : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y => f (x * y)) (GLs n) ∧
      ∀ (w : List (Idx n)), ∀ y ∈ GLs n, Rw w (fun y => f (x * y)) y = Rw w f (x * y) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | exact GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left | (intros; apply GlobalTheory.CompanionTheory.SobGL.LeftTr.Rw_left <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroup

section

@[expose] public section

noncomputable section
open MeasureTheory Matrix Finset
open scoped ContDiff
namespace GlobalTheory.CompanionTheory.SobGL
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bound_on_cube (n : ℕ) (Q : Set (Idx n → ℝ)) (hQc : IsCompact Q) (hQ : ∀ t ∈ Q, 1 + cm t ∈ GLs n)
    (L : List (Idx n)) : ∃ (W : Finset (List (Idx n))) (B : ℝ), 0 ≤ B ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
        ∀ t ∈ Q, ‖Dw L f (1 + cm t)‖ ^ 2 ≤ B * ∑ w ∈ W, ‖Rw w f (1 + cm t)‖ ^ 2 := by
  obtain ⟨m, c, w, hc, hrep⟩ := GlobalTheory.T.derivative_as_right_words n L
  obtain ⟨-, hcm, -, -⟩ := GlobalTheory.T.chart_and_right_words_smooth n
  have hK : IsCompact ((fun t => 1 + cm t) '' Q) := hQc.image (continuous_const.add hcm)
  have hKsub : (fun t => 1 + cm t) '' Q ⊆ GLs n := by
    rintro _ ⟨t, ht, rfl⟩
    exact hQ t ht
  have hb : ∀ i, ∃ M, ∀ y ∈ (fun t => 1 + cm t) '' Q, ‖c i y‖ ≤ M := fun i =>
    hK.exists_bound_of_continuousOn ((hc i).continuousOn.mono hKsub)
  choose M hM using hb
  refine ⟨Finset.univ.image w, (∑ i, M i ^ 2) * m, by positivity, ?_⟩
  intro V _ _ f hf t ht
  have hy : 1 + cm t ∈ GLs n := hQ t ht
  have hyK : 1 + cm t ∈ (fun t => 1 + cm t) '' Q := ⟨t, ht, rfl⟩
  rw [hrep V f hf _ hy]
  have h1 : ‖∑ i, c i (1 + cm t) • Rw (w i) f (1 + cm t)‖ ≤
      ∑ i, M i * ‖Rw (w i) f (1 + cm t)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hM i _ hyK) (norm_nonneg _)
  have h3 : ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 ≤
      (m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by
    have hi : ∀ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 ≤ ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 :=
      fun i => Finset.single_le_sum (f := fun u => ‖Rw u f (1 + cm t)‖ ^ 2)
        (fun u _ => by positivity) (Finset.mem_image_of_mem w (Finset.mem_univ i))
    calc ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2
        ≤ ∑ _i : Fin m, ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hi i
      _ = (m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by simp
  calc ‖∑ i, c i (1 + cm t) • Rw (w i) f (1 + cm t)‖ ^ 2
      ≤ (∑ i, M i * ‖Rw (w i) f (1 + cm t)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, M i ^ 2) * ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, M i ^ 2) * ((m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (∑ i, M i ^ 2) * m * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by ring

theorem sobG : PositivityTheory.RgBcC.SobG := by
  intro n _ _ μ _
  obtain ⟨hGo, hcm, hcm0, hsm⟩ := GlobalTheory.T.chart_and_right_words_smooth n
  set U0 : Set (Idx n → ℝ) := {t | 1 + cm t ∈ GLs n} with hU0def
  have hU0 : IsOpen U0 := hGo.preimage (continuous_const.add hcm)
  have h0 : (0 : Idx n → ℝ) ∈ U0 := by
    show 1 + cm 0 ∈ GLs n
    rw [hcm0, add_zero]
    show Matrix.det (1 : Mat n) ≠ 0
    simp
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU0 0 h0
  set ε : ℝ := δ / 2 with hε
  have hεpos : 0 < ε := by positivity
  set Q : Set (Idx n → ℝ) := Set.Icc 0 (fun _ => ε) with hQdef
  have hQc : IsCompact Q := isCompact_Icc
  have hQU : Q ⊆ U0 := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hεpos.le).mpr fun i => ?_) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
    exact ht.2 i
  have hQG : ∀ t ∈ Q, 1 + cm t ∈ GLs n := fun t ht => hQU ht
  obtain ⟨T, C1, hC1, hsob⟩ := GlobalTheory.T.poincare_value_bound_on_cube (Idx n) ε hεpos
  have hbd := fun L => bound_on_cube n Q hQc hQG L
  choose W B hB hWB using hbd
  have hK : IsCompact ((fun t => 1 + cm t) '' Q) := hQc.image (continuous_const.add hcm)
  have hKsub : (fun t => 1 + cm t) '' Q ⊆ GLs n := by
    rintro _ ⟨t, ht, rfl⟩
    exact hQG t ht
  obtain ⟨hlg, hlgc⟩ := GlobalTheory.T.length_continuous_proper_sublevel n
  obtain ⟨r, hr⟩ := hK.exists_bound_of_continuousOn (hlg.mono hKsub)
  set S : Set (G n) := {y | lg (y : Mat n) ≤ r} with hSdef
  have hSc : IsCompact S := hlgc r
  have hcov : ∀ t ∈ Q, ∃ y ∈ S, (y : Mat n) = 1 + cm t := by
    intro t ht
    have hdet : IsUnit (1 + cm t).det := isUnit_iff_ne_zero.mpr (hQG t ht)
    refine ⟨Matrix.nonsingInvUnit _ hdet, ?_, rfl⟩
    show lg (1 + cm t) ≤ r
    have h := hr _ ⟨t, ht, rfl⟩
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  obtain ⟨C2, hC2, hcmp⟩ := GlobalTheory.T.haar_chart_integral_comparison n μ Q S hQc hSc hcov
  refine ⟨T.biUnion W, r, C1 * C2 * ∑ L ∈ T, B L, ?_⟩
  intro V _ _ _ f hf x hx
  obtain ⟨hgs, hgR⟩ := GlobalTheory.T.left_translate_right_derivative n V f hf x hx
  obtain ⟨hFs, hpd⟩ := GlobalTheory.T.chart_partial_eq_right_word n V (fun y => f (x * y)) hgs
  have hxmul : ∀ y ∈ GLs n, x * y ∈ GLs n := by
    intro y hy
    show Matrix.det (x * y) ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  have hRc : ∀ w, ContinuousOn (Rw w f) (GLs n) := fun w => ((hsm V f hf).1 w).continuousOn
  let φ : Mat n → ℝ := fun y => ∑ w ∈ T.biUnion W, ‖Rw w f (x * y)‖ ^ 2
  have hφc : ContinuousOn φ (GLs n) := by
    apply continuousOn_finsetSum
    intro w _
    exact (((hRc w).comp (continuous_const.mul continuous_id).continuousOn
      (fun y hy => hxmul y hy)).norm).pow 2
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => Finset.sum_nonneg fun _ _ => by positivity
  have hmain := hcmp φ hφc hφ0
  have hF := hsob V U0 (fun t => f (x * (1 + cm t))) hU0 hQU hFs
  have hstep : ∀ L ∈ T, ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 ≤
      B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) := by
    intro L hL
    have hcongr : ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 =
        ∫ t in Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [hpd L t (hQG t ht)])
    rw [hcongr]
    have hle : ∀ t ∈ Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2 ≤ B L * φ (1 + cm t) := by
      intro t ht
      refine (hWB L V (fun y => f (x * y)) hgs t ht).trans (mul_le_mul_of_nonneg_left ?_ (hB L))
      calc ∑ w ∈ W L, ‖Rw w (fun y => f (x * y)) (1 + cm t)‖ ^ 2
          = ∑ w ∈ W L, ‖Rw w f (x * (1 + cm t))‖ ^ 2 :=
            Finset.sum_congr rfl fun w _ => by rw [hgR w _ (hQG t ht)]
        _ ≤ φ (1 + cm t) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem W hL)
              (fun _ _ _ => by positivity)
    have hint : IntegrableOn (fun t => B L * φ (1 + cm t)) Q volume := by
      refine ContinuousOn.integrableOn_compact hQc ?_
      exact continuousOn_const.mul
        (hφc.comp (continuous_const.add hcm).continuousOn (fun t ht => hQG t ht))
    calc ∫ t in Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2
        ≤ ∫ t in Q, B L * φ (1 + cm t) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity) hint
            ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hle))
      _ = B L * ∫ t in Q, φ (1 + cm t) := integral_const_mul _ _
      _ ≤ B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) := mul_le_mul_of_nonneg_left hmain (hB L)
  have hsplit : ∫ y in S, φ (y : Mat n) ∂μ =
      ∑ w ∈ T.biUnion W, ∫ y in S, ‖Rw w f (x * (y : Mat n))‖ ^ 2 ∂μ := by
    refine integral_finsetSum _ fun w _ => ?_
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have hval : ∀ y : G n, x * (y : Mat n) ∈ GLs n := fun y =>
      hxmul _ ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
    exact (((hRc w).comp_continuous (continuous_const.mul Units.continuous_val) hval).norm).pow 2
  have hF0 : f (x * (1 + cm 0)) = f x := by rw [hcm0, add_zero, mul_one]
  calc ‖f x‖ ^ 2 = ‖f (x * (1 + cm 0))‖ ^ 2 := by rw [hF0]
    _ ≤ C1 * ∑ L ∈ T, ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 := hF
    _ ≤ C1 * ∑ L ∈ T, B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hC1
    _ = C1 * C2 * (∑ L ∈ T, B L) * ∫ y in S, φ (y : Mat n) ∂μ := by
        rw [← Finset.sum_mul]
        ring
    _ = C1 * C2 * (∑ L ∈ T, B L) *
        ∑ w ∈ T.biUnion W, ∫ y in S, ‖Rw w f (x * (y : Mat n))‖ ^ 2 ∂μ := by rw [hsplit]

end GlobalTheory.CompanionTheory.SobGL
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroupStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.sobolev_inequality_on_group : PositivityTheory.RgBcC.SobG := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.sobG | exact GlobalTheory.CompanionTheory.SobGL.sobG | (intros; apply GlobalTheory.CompanionTheory.SobGL.sobG <;> assumption)
end
end
