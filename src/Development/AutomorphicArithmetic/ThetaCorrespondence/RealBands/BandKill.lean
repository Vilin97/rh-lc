module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Fourier.Inversion
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.IsBand
public import Mathlib.Analysis.Fourier.FourierTransform

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.EigBand

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.isEig_of_isBand :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] (N : Set G) (a : ℝ → G) (H : G → ℝ) (h : G → ℂ),
      IsRay N a H → IsBand N H h → ∀ s : ℝ, ∃ C : ℝ,
        IsEig N a s C (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) ∧
          ∀ g, Integrable (fun t : ℝ => h (g * a t)) ∧ ∫ t : ℝ, ‖h (g * a t)‖ ≤ C := by
  intro G _ _ _ _ _ _ N a H h hr hb s
  obtain ⟨hc, ⟨B, hB⟩, hN, ⟨R, hR⟩⟩ := hb
  have ha := hr.cont
  have hH := hr.contH
  have he1 : ∀ x : ℝ, ‖Complex.exp (-((x : ℂ) * Complex.I))‖ = 1 := fun x => by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsupp : ∀ g t, h (g * a t) ≠ 0 → |H g + t| ≤ R := fun g t hne => by
    have := hR _ hne
    rwa [hr.move] at this
  have hint : ∀ g, Integrable (fun t : ℝ => h (g * a t)) := by
    intro g
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -R - H g) (b := R - H g)) ?_
    intro t ht
    by_contra hne
    apply ht
    have := abs_le.mp (hsupp g t hne)
    constructor <;> linarith [this.1, this.2]
  have hbound : ∀ g, ∫ t : ℝ, ‖h (g * a t)‖ ≤ 2 * |R| * |B| := by
    intro g
    have hle : ∀ t, ‖h (g * a t)‖ ≤ (Set.Icc (-R - H g) (R - H g)).indicator (fun _ => |B|) t := by
      intro t
      by_cases hne : h (g * a t) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g t hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    refine (integral_mono (hint g).norm
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc) hle).trans ?_
    rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul, Real.volume_real_Icc]
    have h1 : max (R - H g - (-R - H g)) 0 ≤ 2 * |R| :=
      max_le (by linarith [le_abs_self R]) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg B)
  have hshift : ∀ g, (∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
      Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
        ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    intro g
    rw [← integral_const_mul]
    conv_lhs => rw [← integral_sub_right_eq_self _ (H g)]
    congr 1
    ext t
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  have hΦ : Continuous fun g =>
      ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) := by
    refine continuous_of_dominated (bound := (Set.Icc (-R) R).indicator (fun _ => |B|)) ?_ ?_ ?_ ?_
    · intro g
      exact (by fun_prop : Continuous fun t : ℝ =>
        Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g))).aestronglyMeasurable
    · intro g
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, he1, one_mul]
      by_cases hne : h (g * a (t - H g)) = 0
      · rw [hne, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) _
      · have := abs_le.mp (hsupp g _ hne)
        rw [Set.indicator_of_mem (by constructor <;> linarith [this.1, this.2])]
        exact (hB _).trans (le_abs_self B)
    · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    · exact Eventually.of_forall fun t => by fun_prop
  refine ⟨2 * |R| * |B|, ⟨?_, ?_, ?_, ?_⟩, fun g => ⟨hint g, hbound g⟩⟩
  · rw [show (fun g => ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a t)) =
        fun g => Complex.exp (((s * H g : ℝ) : ℂ) * Complex.I) *
          ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * h (g * a (t - H g)) from funext hshift]
    exact (Complex.continuous_exp.comp (by fun_prop)).mul hΦ
  · intro g
    refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hbound g))
    congr 1
    ext t
    rw [norm_mul, he1, one_mul]
  · intro g m hm
    beta_reduce
    congr 1
    ext t
    rw [show g * m * a t = g * a t * ((a t)⁻¹ * m * a t) by group, hN _ _ (hr.norm t m hm)]
  · intro g u
    beta_reduce
    rw [← integral_const_mul]
    conv_rhs => rw [← integral_add_left_eq_self _ u]
    congr 1
    ext t
    rw [mul_assoc g, ← hr.add, ← mul_assoc, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Fourier

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

open scoped FourierTransform in
theorem UpperTheory.Lit.Cusp.fourier_zero :
    ∀ u : ℝ → ℂ, Continuous u → Integrable u →
      (∀ s : ℝ, ∫ t : ℝ, Complex.exp (-((s * t : ℝ) * Complex.I)) * u t = 0) → ∀ t, u t = 0 := by
  intro u hc hi hz t
  have hF : 𝓕 u = 0 := by
    ext w
    rw [Real.fourier_real_eq_integral_exp_smul, Pi.zero_apply, ← hz (2 * Real.pi * w)]
    congr 1
    ext v
    rw [smul_eq_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hinv := hc.fourierInv_fourier_eq hi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  simp [Real.fourierInv_eq]
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BandKill

section

@[expose] public section

open MeasureTheory Filter UpperTheory.Lit.Cusp
open scoped Topology

theorem UpperTheory.Lit.Cusp.conv_band :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (a : ℝ → G) (H : G → ℝ) (f h : G → ℂ),
      IsRay N a H → Continuous f → Integrable f μ → Kills μ N a f → IsBand N H h → ∀ x, conv μ f h x = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ N a H f h hR hf hfi hK hB x
  have ha := hR.cont
  have hh : Continuous h := hB.1
  obtain ⟨B, hBd⟩ := hB.2.1
  obtain ⟨C, -, hC⟩ := isEig_of_isBand G N a H h hR hB 0
  have a0 : a 0 = 1 := by
    have := hR.add 0 0
    rw [add_zero] at this
    simpa using this
  have hFc : Continuous (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) := by fun_prop
  have hF : Integrable (fun p : G × ℝ => f p.1 * h (p.1⁻¹ * x * a p.2)) (μ.prod volume) := by
    rw [integrable_prod_iff hFc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => (hC (g⁻¹ * x)).1.const_mul (f g), ?_⟩
    refine Integrable.mono' (hfi.norm.mul_const C)
      (hFc.norm.aestronglyMeasurable.integral_prod_right') (Eventually.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun t => norm_nonneg _)]
    simp only [norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hC (g⁻¹ * x)).2 (norm_nonneg _)
  have huc : Continuous (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := by
    refine continuous_of_dominated (bound := fun g => ‖f g‖ * B) (fun t => ?_) (fun t => ?_)
      (hfi.norm.mul_const B) (Eventually.of_forall fun g => by fun_prop)
    · exact Continuous.aestronglyMeasurable (by fun_prop)
    · refine Eventually.of_forall fun g => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hBd _) (norm_nonneg _)
  have hui : Integrable (fun t : ℝ => ∫ g, f g * h (g⁻¹ * x * a t) ∂μ) := hF.integral_prod_right
  have key := fourier_zero _ huc hui (fun s => ?_) 0
  · simpa [a0, conv] using key
  obtain ⟨D, hE, -⟩ := isEig_of_isBand G N a H h hR hB s
  have h0 := hK s D _ hE x
  have hF' : Integrable (fun p : G × ℝ =>
      Complex.exp (-((s * p.2 : ℝ) * Complex.I)) * (f p.1 * h (p.1⁻¹ * x * a p.2))) (μ.prod volume) := by
    refine hF.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun p => ?_)
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hsw := integral_integral_swap (μ := μ) (ν := (volume : Measure ℝ))
    (f := fun g t => Complex.exp (-((s * t : ℝ) * Complex.I)) * (f g * h (g⁻¹ * x * a t))) hF'
  simp only [← integral_const_mul]
  rw [← hsw, ← h0, conv]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  ring
end
end
