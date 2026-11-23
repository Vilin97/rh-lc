module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchFactorMulPSeriesEqIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasurablePartitionOfUnityUnitLogTranslateStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeThetaKernelPoissonSummationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableWeightedHeckeThetaKernelHalfSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicBoundedGaussianSummableCmTypeStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableWeightedHeckeThetaKernelHalfSpaceStatement

section

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace : ∀ (I : Type) [Fintype I] {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (q : (I → ℝ) → ℝ) (B R : ℝ), (∃ i, n i ≠ 0) → (∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) → (∃ δ : ℝ, 0 < δ ∧ ∀ j, a j ≠ 0 → e j ≠ 0 → δ ≤ ‖e j‖) → Measurable q → (∀ y, |q y| ≤ B) → (∀ y, q y ≠ 0 → ∀ i j, y i - y j ≤ R) → MeasureTheory.AEStronglyMeasurable (fun y => (q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y) MeasureTheory.volume ∧ ∀ σ : ℝ, MeasureTheory.Integrable (fun y => ‖(q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y‖ * Real.exp (σ * ∑ i, y i)) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) := by
  first | exact @GlobalTheory.HeckeTheta.Decay.integrable_weight_theta | exact GlobalTheory.HeckeTheta.Decay.integrable_weight_theta | (intros; apply GlobalTheory.HeckeTheta.Decay.integrable_weight_theta <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplaceIntegralEntireBoundedInVerticalStrips

section

@[expose] public section

open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.LaplaceStrip

theorem norm_integrand {α : Type} (ℓ : α → ℝ) (g : α → ℂ) (s : ℂ) (x : α) :
    ‖g x * Complex.exp (s * (ℓ x : ℂ))‖ = ‖g x‖ * Real.exp (s.re * ℓ x) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem laplace_entire_boundedInStrips {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ)
    (hℓ : Measurable ℓ) (hg : MeasureTheory.AEStronglyMeasurable g μ) (hpos : ∀ᵐ x ∂μ, 0 ≤ ℓ x)
    (hint : ∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    hg.mul (by fun_prop : Measurable fun x => Complex.exp (s * (ℓ x : ℂ))).aestronglyMeasurable
  have hI : ∀ s : ℂ, Integrable (fun x => g x * Complex.exp (s * (ℓ x : ℂ))) μ := fun s =>
    (hint s.re).mono' (hmeas s) (Filter.Eventually.of_forall fun x => (norm_integrand ℓ g s x).le)
  refine ⟨fun s₀ => ?_, fun a b _ => ⟨∫ x, ‖g x‖ * Real.exp (b * ℓ x) ∂μ, fun s _ hsb => ?_⟩⟩
  · have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x => g x * Complex.exp (s * (ℓ x : ℂ)))
      (F' := fun s x => g x * (Complex.exp (s * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))))
      (x₀ := s₀) (bound := fun x => ‖g x‖ * Real.exp ((s₀.re + 2) * ℓ x)) (Metric.ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall hmeas) (hI s₀)
      (hg.mul (by fun_prop : Measurable fun x =>
        Complex.exp (s₀ * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))).aestronglyMeasurable)
      ?_ (hint _) ?_
    · exact key.2.differentiableAt
    · filter_upwards [hpos] with x hx s hs
      have hre : s.re ≤ s₀.re + 1 := by
        have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
        have h2 : ‖s - s₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hs
        have h3 := (abs_le.mp h1).2
        simp only [Complex.sub_re] at h3
        linarith
      rw [one_mul, ← mul_assoc, norm_mul, norm_integrand, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
      have e1 : Real.exp (s.re * ℓ x) ≤ Real.exp ((s₀.re + 1) * ℓ x) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre hx)
      have e2 : ℓ x ≤ Real.exp (ℓ x) := by linarith [Real.add_one_le_exp (ℓ x)]
      have e3 : Real.exp ((s₀.re + 2) * ℓ x) = Real.exp ((s₀.re + 1) * ℓ x) * Real.exp (ℓ x) := by
        rw [← Real.exp_add]; ring_nf
      rw [e3, mul_assoc]
      gcongr
    · exact Filter.Eventually.of_forall fun x s _ => by
        have := (((hasDerivAt_id s).mul_const (ℓ x : ℂ)).cexp).const_mul (g x)
        simpa using this
  · refine norm_integral_le_of_norm_le (hint b) ?_
    filter_upwards [hpos] with x hx
    rw [norm_integrand]
    gcongr

end GlobalTheory.LaplaceStrip
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplaceIntegralEntireBoundedInVerticalStripsStatement

section

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips : ∀ {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ), Measurable ℓ → MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, 0 ≤ ℓ x) → (∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) → Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  first | exact @GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | exact GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | (intros; apply GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinIntegralSplitFunctionalEquation

section

@[expose] public section

open NumberField MeasureTheory

namespace GlobalTheory

theorem mellinSplit_hyperplane_null (I : Type) [Fintype I] [Nonempty I] :
    (volume : Measure (I → ℝ)) {y : I → ℝ | ∑ i, y i = 0} = 0 := by
  let L : (I → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have hL : ∀ y, L y = ∑ i, y i := by intro y; simp [L]
  have hset : {y : I → ℝ | ∑ i, y i = 0} = (LinearMap.ker L : Set (I → ℝ)) := by
    ext y; simp [hL]
  rw [hset]
  apply Measure.addHaar_submodule
  intro htop
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty I)
  have hmem : Pi.single i (1:ℝ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hmem
  simp at hmem

theorem mellinSplit_neg (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ)
    (hθ : ∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y))
    (h1 : MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}))
    (h2 : MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i})) :
    ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  set f : (I → ℝ) → ℂ := fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf
  set g : (I → ℝ) → ℂ := fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) with hg
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hS
  set P : Set (I → ℝ) := {y | 0 < ∑ i, y i} with hP
  have hcont : Continuous (fun y : I → ℝ => ∑ i, y i) :=
    continuous_finsetSum _ fun i _ => continuous_apply i
  have hSm : MeasurableSet S := (isClosed_le continuous_const hcont).measurableSet
  have hsumneg : ∀ y : I → ℝ, ∑ i, (-y) i = -∑ i, y i := by
    intro y; simp [Finset.sum_neg_distrib]
  have hfg : ∀ y, f y = κ * g (-y) := by
    intro y
    simp only [hf, hg, hθ, neg_neg, hsumneg]
    have e : Complex.exp (-((∑ i, y i : ℝ) : ℂ)) * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))
        = Complex.exp ((1 - s) * ((-∑ i, y i : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; push_cast; ring_nf
    have e2 : ((Real.exp (-∑ i, y i) : ℝ) : ℂ) = Complex.exp (-((∑ i, y i : ℝ) : ℂ)) := by
      push_cast; rfl
    rw [e2]
    linear_combination ((p y : ℂ) * κ * θ' (-y)) * e
  have hpre : (Neg.neg : (I → ℝ) → (I → ℝ)) ⁻¹' P = Sᶜ := by
    ext y; simp [hP, hS, hsumneg]
  have hmp : MeasurePreserving (Neg.neg : (I → ℝ) → (I → ℝ)) volume volume :=
    Measure.measurePreserving_neg _
  have hemb : MeasurableEmbedding (Neg.neg : (I → ℝ) → (I → ℝ)) :=
    (MeasurableEquiv.neg (I → ℝ)).measurableEmbedding
  have hPS : P =ᵐ[volume] S := by
    rw [ae_eq_set]
    constructor
    · have : P \ S = ∅ := Set.diff_eq_empty.mpr (fun y (hy : 0 < ∑ i, y i) => (le_of_lt hy : 0 ≤ ∑ i, y i))
      rw [this, measure_empty]
    · apply measure_mono_null _ (mellinSplit_hyperplane_null I)
      intro y hy
      simp only [hP, hS, Set.mem_diff, Set.mem_setOf_eq, not_lt] at hy
      exact le_antisymm hy.2 hy.1
  have hgP : IntegrableOn g P volume :=
    IntegrableOn.congr_set_ae (show IntegrableOn g S volume from h2) hPS
  have hfc : IntegrableOn f Sᶜ volume := by
    have := (hmp.integrableOn_comp_preimage hemb).2 hgP
    rw [hpre] at this
    have h3 := this.const_mul κ
    refine IntegrableOn.congr_fun h3 (fun y _ => ?_) hSm.compl
    simp [hfg y]
  have hfint : Integrable f volume := by
    have := IntegrableOn.union (show IntegrableOn f S volume from h1) hfc
    rwa [Set.union_compl_self, integrableOn_univ] at this
  rw [← integral_add_compl hSm hfint]
  congr 1
  calc ∫ y in Sᶜ, f y = ∫ y in Sᶜ, κ * g (-y) := by simp_rw [hfg]
    _ = κ * ∫ y in Sᶜ, g (-y) := integral_const_mul _ _
    _ = κ * ∫ y in P, g y := by
        rw [← hpre, hmp.setIntegral_preimage_emb hemb]
    _ = κ * ∫ y in S, g y := by rw [setIntegral_congr_set hPS]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinIntegralSplitFunctionalEquationStatement

section

@[expose] public section

open NumberField MeasureTheory

theorem _root_.GlobalTheory.T.mellin_integral_split_functional_equation : ∀ (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ), (∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y)) → MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.mellinSplit_neg | exact GlobalTheory.mellinSplit_neg | (intros; apply GlobalTheory.mellinSplit_neg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStrips

section

@[expose] public section

noncomputable section
open NumberField MeasureTheory

namespace GlobalTheory.HeckeStrip

theorem completed_pSeries_entire_bounded : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  intro K _ _ _ I _ φ hφ n hn M F hM hper hinv
  haveI : Nonempty I := ⟨hn.choose⟩
  obtain ⟨p, hpm, hp0, hpsum, R, hpR⟩ := GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates K I φ hφ
  obtain ⟨⟨C, hC⟩, hsumm, hge⟩ := GlobalTheory.T.periodic_bounded_gaussian_summable_cmType K I φ hφ M F hM hper
  obtain ⟨a, κ, hasumm, ⟨δ, hδ, hδa⟩, hfe⟩ := GlobalTheory.T.heckeThetaKernel_poisson_summation K I φ hφ n M F hM hper
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hpsum y) 1 (fun u _ => hp0 _)
    have h0 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by
      funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h0] using h
  have hpB : ∀ y, |p y| ≤ 1 := fun y => abs_le.2 ⟨by linarith [hp0 y], hp1 y⟩
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hℓ : Measurable (fun y : I → ℝ => ∑ i, y i) := by fun_prop
  have hS0 : ∀ᵐ y ∂(volume.restrict S), 0 ≤ ∑ i, y i := ae_restrict_of_forall_mem hSm fun y hy => hy
  obtain ⟨D1m, D1i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n p 1 R hn hsumm
    ⟨1, one_pos, fun α _ h => hge α h⟩ hpm hpB hpR
  obtain ⟨D2m, D2i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun v : I → ℂ => v) a n (fun y => p (-y)) 1 R hn hasumm ⟨δ, hδ, hδa⟩
    (hpm.comp measurable_neg) (fun y => hpB _) (fun y hy i j => by
      have := hpR (-y) hy j i
      simp only [Pi.neg_apply] at this
      linarith)
  have A1 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D1m.restrict hS0 D1i
  have A2 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D2m.restrict hS0 D2i
  have hint : ∀ (g : (I → ℝ) → ℂ) (t : ℂ), AEStronglyMeasurable g volume →
      (∀ σ : ℝ, Integrable (fun y => ‖g y‖ * Real.exp (σ * ∑ i, y i)) (volume.restrict S)) →
      Integrable (fun y => g y * Complex.exp (t * ((∑ i, y i : ℝ) : ℂ))) (volume.restrict S) := by
    intro g t hg hgi
    refine (hgi t.re).mono' (hg.restrict.mul (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]
  set f1 : ℂ → ℂ := fun s => ∫ y in S, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf1
  set f2 : ℂ → ℂ := fun s => ∫ y in S, (p (-y) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf2
  have hd1 : Differentiable ℂ f1 := A1.1
  have hd2 : Differentiable ℂ f2 := A2.1
  have hb1 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f1 := A1.2
  have hb2 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f2 := A2.2
  refine ⟨fun s => 2 ^ Fintype.card I * (f1 s + κ * f2 (1 - s)), ?_, ?_, ?_⟩
  · exact (hd1.add ((hd2.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul κ)).const_mul _
  · intro a' b' hab
    obtain ⟨C1, hC1⟩ := hb1 a' b' hab
    obtain ⟨C2, hC2⟩ := hb2 (1 - b') (1 - a') (by linarith)
    refine ⟨‖(2 : ℂ) ^ Fintype.card I‖ * (C1 + ‖κ‖ * C2), fun s h1 h2 => ?_⟩
    rw [norm_mul]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add (hC1 s h1 h2) ?_)
    rw [norm_mul]
    gcongr
    exact hC2 (1 - s) (by simp; linarith) (by simp; linarith)
  · intro s hs
    rw [GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt K I φ hφ n hn F C hC hinv p hpm hp0 hpsum s hs,
      GlobalTheory.T.mellin_integral_split_functional_equation I p _ _ κ s hfe (hint _ s D1m D1i) (hint _ (1 - s) D2m D2i)]

end GlobalTheory.HeckeStrip
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStripsStatement

section

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.completed_heckePartialLSeries_entire_bounded_strips : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  first | exact @GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | exact GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded | (intros; apply GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded <;> assumption)
end
end
