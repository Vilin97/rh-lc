module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
public import GroundTheory.AutomorphicForms.TraceFormulaConvolution
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CenterC
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Smoothing
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.DerivInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InvSmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactSpec
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RightDerivConvComm
import Mathlib.Tactic.TypeStar

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.ConvL

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.ConvolutionTheory.Tf.convL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : CompactlySupportedContinuousMap (archGroup K n) ℂ)
      (h₁ : (fun g => β₁ g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)), ∃ h₁₂ : (fun g => conv ν β₁ β₂ g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ), ∀ (u : UEnv K n) (x : archGroup K n),
        ((isExpLieAlgebra K n).rightUAction u ⟨fun g => conv ν β₁ β₂ g⁻¹, h₁₂⟩ : archGroup K n → ℂ) x⁻¹ =
          ∫ a, ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β₁ g⁻¹, h₁⟩ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x) ∂ν := by
  intro K _ _ n ν _ β₁ β₂ h₁
  have hc : HasCompactSupport (fun g : archGroup K n => β₁ g⁻¹) :=
    β₁.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
  have hΘ : Continuous (fun c : archGroup K n => β₂ c⁻¹) := (map_continuous β₂).comp continuous_inv
  obtain ⟨hF, hD⟩ := UpperTheory.ConvolutionTheory.Tf.derivInt K n ν (fun g => β₁ g⁻¹) h₁ hc (fun c => β₂ c⁻¹) hΘ
  have e : (fun x : archGroup K n => ∫ a, (fun g : archGroup K n => β₁ g⁻¹) (a⁻¹ * x) * (fun c : archGroup K n => β₂ c⁻¹) a ∂ν) =
      fun g => conv ν β₁ β₂ g⁻¹ := by
    funext g
    rw [GroundTheory.Automorphic.conv_apply,
      ← integral_mul_left_eq_self (μ := ν) (fun a => β₁ a * β₂ (a⁻¹ * g⁻¹)) g⁻¹]
    congr 1
    funext c
    simp [mul_assoc]
  refine ⟨e ▸ hF, fun u x => ?_⟩
  refine Eq.trans (congrArg (fun f => (((isExpLieAlgebra K n).rightUAction u f :
    (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) x⁻¹) (Subtype.ext e.symm : _ = (⟨_, hF⟩ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)))) ?_
  rw [hD u x⁻¹, ← integral_mul_left_eq_self (μ := ν) (fun a =>
    ((isExpLieAlgebra K n).rightUAction u ⟨fun g => β₁ g⁻¹, h₁⟩ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x)) x]
  congr 1
  funext c
  simp [mul_assoc]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactConv

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section SlopeTestRemainingChoices

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [BorelSpace G] [IsFiniteMeasureOnCompacts μ]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem lactConv_integrable (f g : CompactlySupportedContinuousMap G ℂ) (x : G) :
    Integrable (fun a => f a * g (a⁻¹ * x)) μ := by
  have hc : Continuous fun a => f a * g (a⁻¹ * x) :=
    (map_continuous f).mul ((map_continuous g).comp (continuous_inv.mul continuous_const))
  exact hc.integrable_of_hasCompactSupport (f.hasCompactSupport.mul_right)

private theorem lactConv_left (f f' g : CompactlySupportedContinuousMap G ℂ) (c : ℂ) :
    conv μ (f + c • f') g = conv μ f g + c • conv μ f' g := by
  ext x
  simp only [conv_apply, CompactlySupportedContinuousMap.add_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (lactConv_integrable μ f g x) ((lactConv_integrable μ f' g x).const_mul c)]
  congr 1
  funext a
  ring

private theorem lactConv_right (f g g' : CompactlySupportedContinuousMap G ℂ) (c : ℂ) :
    conv μ f (g + c • g') = conv μ f g + c • conv μ f g' := by
  ext x
  simp only [conv_apply, CompactlySupportedContinuousMap.add_apply, CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  rw [← integral_const_mul, ← integral_add (lactConv_integrable μ f g x) ((lactConv_integrable μ f g' x).const_mul c)]
  congr 1
  funext a
  ring

end SlopeTestRemainingChoices

private theorem lactConv_split {K : Type} [Field K] [NumberField K] {n : ℕ} (β : TI K n) (hβ : SmoothT β) (a b : UEnv K n) :
    lact ((1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b) β = lact ((1 : ℂ) ⊗ₜ[ℝ] a) β + Complex.I • lact ((1 : ℂ) ⊗ₜ[ℝ] b) β := by
  obtain ⟨_, -, -, -, h4, h5, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  have e : (Complex.I ⊗ₜ[ℝ] b : UC K n) = Complex.I • ((1 : ℂ) ⊗ₜ[ℝ] b) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [(h4 _ _).2, e, (h5 _ _).1]

theorem UpperTheory.ConvolutionTheory.Tf.lactConv :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : TI K n), SmoothT β₁ →
      SmoothT (conv ν β₁ β₂) ∧ (∀ u, lact u (conv ν β₁ β₂) = conv ν (lact u β₁) β₂) ∧
      (IsTotallyComplex K → SmoothT β₂ → ∀ z ∈ Subalgebra.center ℂ (UC K n), conv ν (lact z β₁) β₂ = conv ν β₁ (lact z β₂)) := by
  intro K _ _ n ν _ β₁ β₂ hβ₁
  obtain ⟨h₁, -, -, -, -, -, -, e₁⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β₁ hβ₁
  obtain ⟨h₁₂, hL⟩ := UpperTheory.ConvolutionTheory.Tf.convL K n ν β₁ β₂ h₁
  have hs : SmoothT (conv ν β₁ β₂) := by
    have h := (UpperTheory.ConvolutionTheory.Tf.invSmooth K n _ h₁₂).1
    simp only [inv_inv] at h
    exact h
  refine ⟨hs, ?_, ?_⟩
  · obtain ⟨h', -, -, -, -, -, -, e'⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ hs
    have key : ∀ a : UEnv K n, lact ((1 : ℂ) ⊗ₜ[ℝ] a) (conv ν β₁ β₂) = conv ν (lact ((1 : ℂ) ⊗ₜ[ℝ] a) β₁) β₂ := by
      intro a
      ext x
      rw [e', hL, conv_apply]
      simp only [e₁]
    intro u
    obtain ⟨a, b, rfl⟩ := (UpperTheory.ConvolutionTheory.Tf.centerC (UEnv K n) u).1
    rw [lactConv_split _ hs, lactConv_split _ hβ₁, lactConv_left, key, key]
  · intro hK hβ₂ z hz
    obtain ⟨h₂, -, -, -, -, -, -, e₂⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β₂ hβ₂
    have key : ∀ a ∈ Subalgebra.center ℝ (UEnv K n),
        conv ν (lact ((1 : ℂ) ⊗ₜ[ℝ] a) β₁) β₂ = conv ν β₁ (lact ((1 : ℂ) ⊗ₜ[ℝ] a) β₂) := by
      intro a ha
      ext x
      rw [conv_apply, conv_apply]
      simp only [e₁, e₂]
      exact UpperTheory.ConvolutionTheory.Tf.convZ K n ν β₁ β₂ h₁ h₂ a ha x
    obtain ⟨⟨a, b, hab⟩, hc⟩ := UpperTheory.ConvolutionTheory.Tf.centerC (UEnv K n) z
    obtain ⟨ha, hb⟩ := (hc a b hab).1 hz
    rw [hab, lactConv_split _ hβ₁, lactConv_split _ hβ₂, lactConv_left, lactConv_right, key a ha, key b hb]
end
end
