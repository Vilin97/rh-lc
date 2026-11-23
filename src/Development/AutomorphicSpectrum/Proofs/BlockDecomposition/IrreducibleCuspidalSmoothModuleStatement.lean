module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLinearCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivativeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRepStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2ConvolutionLocallyCompactMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegral
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormDerivativeModerateGrowth

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2ConvolutionLocallyCompactMemStatement

section

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace

theorem _root_.GlobalTheory.T.l2_convolution_locally_compact_mem : ∀ {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [SecondCountableTopology L] [T2Space L] [LocallyCompactSpace L] [MeasurableSpace L] [BorelSpace L] (ν : Measure L) [IsFiniteMeasureOnCompacts ν] (j : L →* G), Continuous j → ∀ D : L → ℂ, Continuous D → HasCompactSupport D → ∀ φ ψ : G → ℂ, Continuous φ → ∀ h : MemL2Quotient Γ μ φ, (∀ g, ψ g = ∫ y, φ (g * j y) * D y ∂ν) → ∃ h' : MemL2Quotient Γ μ ψ, ∀ W : Submodule ℂ (L2 Γ μ), IsSubrep (R Γ μ) W → h.toL2 ∈ W → h'.toL2 ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem | exact GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem | (intros; apply GlobalTheory.CompanionTheory.AutomorphicL2Convolution.memL2_convolution_mem <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieDerivativeConvolutionKernel

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.LieConv

theorem mMap_surjective (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Function.Surjective (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a) := fun X =>
  ⟨(fun i j => ((0, fun w => X i j w.1) : mixedEmbedding.mixedSpace E) :
    Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), rfl⟩

theorem exists_kernel_basis (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ)
    (j : Fin (CuspidalSpectrum.archDim E a)) :
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a,
      (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (CuspidalSpectrum.archBasis E a j)) φ).1 g =
        ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  obtain ⟨D, hD, hDc, h⟩ := GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ) hφ ν 1
    (fun _ => j)
  refine ⟨D, hD, hDc, fun g => ?_⟩
  rw [← h g, CuspidalSpectrum.uAction_uJ_succ]
  have e := GlobalTheory.CompanionTheory.HCRep.smL_liB (E := E) (a := a) (CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis E a j)) φ
  have e2 := congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1 g) e
  have e0 : ∀ ψ : AutomorphicForm.archSmooth E a,
      AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) 0 (Fin.tail fun _ => j)) ψ = ψ := fun ψ => by
    rw [CuspidalSpectrum.uJ, map_one]
    rfl
  rw [e0]
  exact e2

theorem hasCompactSupport_sum {G ι : Type*} [TopologicalSpace G] (s : Finset ι) (c : ι → ℂ) (D : ι → G → ℂ)
    (h : ∀ j, HasCompactSupport (D j)) : HasCompactSupport fun y => ∑ j ∈ s, c j * D j y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((h j).mul_left (f := fun _ => c j)).add ih

theorem lie_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a), IsAutForm φ → ∀ X : Lie E a, ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a, (lie E a X φ).1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  intro E _ _ _ a _ _ ν _ φ hφ X
  obtain ⟨Y, rfl⟩ := mMap_surjective E a X
  choose D hD hDc hconv using exists_kernel_basis E a ν φ hφ
  set b := CuspidalSpectrum.archBasis E a with hb
  set c : Fin (CuspidalSpectrum.archDim E a) → ℂ := fun j => ((b.repr Y j : ℝ) : ℂ) with hc
  refine ⟨fun y => ∑ j, c j * D j y, continuous_finsetSum _ fun j _ => continuous_const.mul (hD j),
    hasCompactSupport_sum _ c D hDc, fun g => ?_⟩
  have hf : Continuous fun y => φ.1 (g * AutomorphicForm.infEmb E a y) :=
    IsExpLieAlgebra.continuous_of_isSmoothFun (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ g)
  have hint : ∀ j, Integrable (fun y => φ.1 (g * AutomorphicForm.infEmb E a y) * D j y) ν := fun j =>
    (hf.mul (hD j)).integrable_of_hasCompactSupport ((hDc j).mul_left)
  have hY : (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a Y) φ).1 g =
      ∑ j, c j * (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (b j)) φ).1 g := by
    conv_lhs => rw [← b.sum_repr Y]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
    Complex.real_smul, hc]
  rw [hY]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hconv j g, ← integral_const_mul]
    congr 1
    funext y
    ring
  · exact ((hint j).const_mul (c j)).congr (Filter.Eventually.of_forall fun y => by ring)

end GlobalTheory.CompanionTheory.LieConv
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieDerivativeConvolutionKernelStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

theorem _root_.GlobalTheory.T.lie_derivative_convolution_kernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a), IsAutForm φ → ∀ X : Lie E a, ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a, (lie E a X φ).1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.LieConv.lie_eq_conv | exact GlobalTheory.CompanionTheory.LieConv.lie_eq_conv | (intros; apply GlobalTheory.CompanionTheory.LieConv.lie_eq_conv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModerateGrowthConvolutionIntegralStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

theorem _root_.GlobalTheory.T.moderate_growth_convolution_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ ψ : GA E a → ℂ), Continuous φ → (∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ (g * infGL E a y)‖ ≤ C * height y ^ N) → ∀ D : AutomorphicForm.archGroup E a → ℂ, Continuous D → HasCompactSupport D → (∀ g, ψ g = ∫ y, φ (g * AutomorphicForm.infEmb E a y) * D y ∂ν) → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖ψ (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.CompanionTheory.GrowthConv.growth_conv | exact GlobalTheory.CompanionTheory.GrowthConv.growth_conv | (intros; apply GlobalTheory.CompanionTheory.GrowthConv.growth_conv <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalSmoothModule

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section
namespace GlobalTheory.CompanionTheory.StableMod

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isCuspForm_fin (k : GL (Fin a) (Af E)) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (finRep E a k φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * finGL E a k) = φ.1 (g * finGL E a k)
    rw [mul_assoc, hA.left]
  · have e : {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ} =
        (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E a k' φ = φ} := by
      ext k'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · intro e
        rw [Module.End.mul_apply, Module.End.mul_apply, e, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
          map_one, Module.End.one_apply]
      · intro e
        have := congrArg (finRep E a k) e
        rwa [Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply (finRep E a k), ← map_mul,
          mul_inv_cancel, map_one, Module.End.one_apply] at this
    change IsOpen {k' | finRep E a k' (finRep E a k φ) = finRep E a k φ}
    rw [e]
    exact hA.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E a c φ)).map
      (finRep E a k)) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
  · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := hA.growth (g * finGL E a k)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * finGL E a k)‖ ≤ _
    rw [mul_assoc, infGL_comm, ← mul_assoc]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * finGL E a k) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * finGL E a k)

theorem isCuspForm_cpt (c : Kinf E a) {φ : Sm E a} (h : IsCuspForm φ) : IsCuspForm (cptRep E a c φ) := by
  open GlobalTheory.CuspStab in
  obtain ⟨hA, hC⟩ := h
  refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · change φ.1 (ratGL E a γ * g * infGL E a (Unitary.toUnits c)) = φ.1 (g * infGL E a (Unitary.toUnits c))
    rw [mul_assoc, hA.left]
  · exact level_of_le hA.level fun k hk => by
      change finRep E a k (cptRep E a c φ) = cptRep E a c φ
      rw [← Module.End.mul_apply, fin_cpt_comm, Module.End.mul_apply, hk]
  · have := hA.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E a c φ))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨c', rfl⟩
    refine Submodule.subset_span ⟨c' * c, ?_⟩
    change _ = (cptRep E a c' * cptRep E a c) φ
    rw [← map_mul]
  · exact zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_compactRep E a c z hz) hA.zfin
  · obtain ⟨C, N, h1⟩ := growth_mul (Unitary.toUnits c) (hA.growth g)
    refine ⟨C, N, fun y => ?_⟩
    change ‖φ.1 (g * infGL E a y * infGL E a (Unitary.toUnits c))‖ ≤ _
    rw [mul_assoc, ← map_mul]
    exact h1 y
  · intro r h0 h1 _ _ μ 𝓕 hμ hF g
    change ∫ x in 𝓕, φ.1 (unip x * g * infGL E a (Unitary.toUnits c)) ∂μ = 0
    simp_rw [mul_assoc]
    exact hC r h0 h1 μ 𝓕 hμ hF (g * infGL E a (Unitary.toUnits c))

theorem lieD_left {φ : Sm E a} (X : Lie E a) {u : GA E a} (hu : ∀ g, φ.1 (u * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (u * g) = (lie E a X φ).1 g := by
  change lieD X φ.1 (u * g) = lieD X φ.1 g
  have e : chart φ.1 (u * g) = chart φ.1 g := by
    funext x
    unfold chart
    split_ifs
    · rw [mul_assoc, hu]
    · rfl
  unfold lieD
  rw [e]

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
  (H : Submodule ℂ (L2 (latticeGL E a) μ))

def formSpace (hH : IsSubrep (R (latticeGL E a) μ) H) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
    ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H}
  zero_mem' := by
    refine ⟨⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩, fun _ _ => rfl, ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (0 : Sm E a).1 := ⟨fun _ _ _ => rfl, MemLp.zero⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = 0 := MemLp.toLp_zero _
    rw [this]
    exact zero_mem _
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3, h4⟩ ⟨h5, h6, h7, h8⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a 1 φ ψ h1 h5
    rw [one_smul] at e
    refine ⟨e, fun t g => ?_, ?_⟩
    · exact congrArg₂ (· + ·) (h2 t g) (h6 t g)
    · have h : MemL2Quotient (latticeGL E a) μ (φ + ψ).1 := ⟨fun γ hγ g => congrArg₂ (· + ·) (h3.1 γ hγ g) (h7.1 γ hγ g), h3.2.add h7.2⟩
      refine ⟨h, ?_⟩
      have : h.toL2 = h3.toL2 + h7.toL2 := MemLp.toLp_add h3.2 h7.2
      rw [this]
      exact add_mem h4 h8
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3, h4⟩
    have hz : IsCuspForm (0 : Sm E a) :=
      ⟨isAutForm_const (zero_mem _), fun r _ _ _ _ _ _ _ _ _ => integral_zero _ _⟩
    have e := GlobalTheory.CuspFormLin.isCuspForm_smul_add E a c φ 0 h1 hz
    rw [add_zero] at e
    refine ⟨e, fun t g => congrArg (c • ·) (h2 t g), ?_⟩
    have h : MemL2Quotient (latticeGL E a) μ (c • φ).1 := ⟨fun γ hγ g => congrArg (c • ·) (h3.1 γ hγ g), h3.2.const_smul c⟩
    refine ⟨h, ?_⟩
    have : h.toL2 = c • h3.toL2 := MemLp.toLp_const_smul c h3.2
    rw [this]
    exact H.smul_mem c h4


open GroundTheory.Automorphic in
theorem exists_stable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)) (_ : H ≤ L2cusp μ)
    (hi : IsIrredSubrep (R (latticeGL E a) μ) H) :
    ∃ V : Submodule ℂ (Sm E a), (∀ φ, φ ∈ V ↔ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧
      ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) ∧ _root_.GlobalTheory.CuspRep.IsStable V := by
  have hS : IsSubrep (R (latticeGL E a) μ) H := hi.1
  refine ⟨formSpace μ H hS, fun φ => Iff.rfl, ?_⟩
  rintro o φ ⟨h1, h2, h3, h4⟩
  cases o with
  | fin k =>
    refine ⟨isCuspForm_fin k h1, fun t g => ?_, h3.mul_right (finGL E a k), ?_⟩
    · change φ.1 (splitCentre E a t * g * finGL E a k) = φ.1 (g * finGL E a k)
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | cpt k =>
    refine ⟨isCuspForm_cpt k h1, fun t g => ?_, h3.mul_right (infGL E a (Unitary.toUnits k)), ?_⟩
    · change φ.1 (splitCentre E a t * g * infGL E a (Unitary.toUnits k)) = φ.1 (g * infGL E a (Unitary.toUnits k))
      rw [mul_assoc, h2]
    · exact (right_translate_toL2 h3 _) ▸ hS.2 _ _ h4
  | lie X =>
    letI : MeasurableSpace (AutomorphicForm.archGroup E a) := borel _
    haveI : BorelSpace (AutomorphicForm.archGroup E a) := ⟨rfl⟩
    obtain ⟨D, hD, hDc, hrep⟩ := GlobalTheory.T.lie_derivative_convolution_kernel E a (Measure.haar : Measure (AutomorphicForm.archGroup E a)) φ h1.1 X
    have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ h1.1.level
    obtain ⟨h', hW⟩ := GlobalTheory.T.l2_convolution_locally_compact_mem (latticeGL E a) μ (Measure.haar : Measure (AutomorphicForm.archGroup E a))
      (AutomorphicForm.infEmb E a) AutomorphicForm.continuous_infEmb D hD hDc φ.1 (lie E a X φ).1 hc h3 hrep
    refine ⟨⟨⟨fun γ g => lieD_left X (h1.1.left γ) g, ?_, GlobalTheory.T.finiteDimensional_span_compact_orbit_lieDerivative E a X φ h1.1.kfin,
      GlobalTheory.CuspStab.zfin_of_comm _ (fun z hz => GlobalTheory.T.mem_zalg_commute_lie_action E a X z hz) h1.1.zfin,
      GlobalTheory.T.moderate_growth_convolution_integral E a _ φ.1 _ hc h1.1.growth D hD hDc hrep⟩, GlobalTheory.T.isCuspidal_lieAction_of_isCuspForm E a X φ h1⟩,
      fun t g => lieD_left X (h2 t) g, h', hW H hS h4⟩
    exact GlobalTheory.CuspStab.level_of_le h1.1.level fun k hk => by
      change finRep E a k (lie E a X φ) = lie E a X φ
      change (rt E a (finGL E a k) * lie E a X) φ = _
      rw [← lie_rt_fin, Module.End.mul_apply]
      exact congrArg (lie E a X) hk

end GlobalTheory.CompanionTheory.StableMod
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleCuspidalSmoothModuleStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.irreducible_cuspidal_smooth_module : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∃ V : Submodule ℂ (Sm E a), (∀ φ, φ ∈ V ↔ IsCuspForm φ ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ ∃ h : MemL2Quotient (latticeGL E a) μ φ.1, h.toL2 ∈ H) ∧ _root_.GlobalTheory.CuspRep.IsStable V := by
  first | exact @GlobalTheory.CompanionTheory.StableMod.exists_stable | exact GlobalTheory.CompanionTheory.StableMod.exists_stable | (intros; apply GlobalTheory.CompanionTheory.StableMod.exists_stable <;> assumption)
end
end
