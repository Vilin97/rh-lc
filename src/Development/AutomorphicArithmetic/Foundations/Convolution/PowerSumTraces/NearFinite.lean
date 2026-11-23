module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
public import GroundTheory.AutomorphicForms.GKModules.Casimir
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsSignedBasisLieSubalgebraExpCompact
public import Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalCuspFormsOfLevelAndDerivOpBound
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
public import Development.AutomorphicArithmetic.TwistedTraces.NormCuspVecLGkActionLeOfAevalEqZero
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.CasimirEqOfOrthonormalBases

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.casimir_eq_of_orthonormal_bases :
    ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L) (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (b' : Module.Basis ι' ℝ L) (ε' : ι' → ℝ), (∀ X Y, B X Y = B Y X) → (∀ i, ε i * ε i = 1) → (∀ i j, B (b i) (b j) = if i = j then ε i else 0) → (∀ i, ε' i * ε' i = 1) → (∀ i j, B (b' i) (b' j) = if i = j then ε' i else 0) → casimir b ε = casimir b' ε' := by
  intro L _ _ B ι ι' _ _ _ _ b ε b' ε' hs hε hb hε' hb'
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L) with hu
  have e1 : ∀ i, u (b i) = ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) := by
    intro i
    conv_lhs => rw [eq_sum_of_orthogonal hε' hb' (b i)]

    simp only [map_sum, map_smul]
  have e2 : ∀ j, u (b' j) = ∑ i, (ε i * B (b i) (b' j)) • u (b i) := by
    intro j
    conv_lhs => rw [eq_sum_of_orthogonal hε hb (b' j)]

    simp only [map_sum, map_smul]
  simp only [casimir]
  calc ∑ i, ε i • (u (b i) * u (b i))
      = ∑ i, ∑ j, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h : u (b i) * u (b i) = u (b i) * ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) :=
          congrArg (fun x => u (b i) * x) (e1 i)
        rw [h, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul_comm, smul_smul]
    _ = ∑ j, ∑ i, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := Finset.sum_comm
    _ = ∑ j, ε' j • (u (b' j) * u (b' j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h : u (b' j) * u (b' j) = (∑ i, (ε i * B (b i) (b' j)) • u (b i)) * u (b' j) :=
          congrArg (fun x => x * u (b' j)) (e2 j)
        rw [h, Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, smul_smul, hs (b' j) (b i)]
        congr 1
        ring
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.NormApplyLeOfLaplacianLowerBound

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_apply_le_of_laplacian_lower_bound :
    ∀ (d : ℕ) (c C : ℝ) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) → ∃ C' : ℝ, ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (A : Fin d → Module.End ℂ M), (∀ i, ∀ x ∈ V, A i x ∈ V) → (∀ i, ∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (A i x)) (j y) + inner ℂ (j x) (j (A i y)) = 0) → ∀ v ∈ V, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re → (∀ i, ε i = -1 → ‖j (A i v)‖ ≤ C * ‖j v‖) → ∀ i, ‖j (A i v)‖ ≤ C' * ‖j v‖ := by
  intro d c C ε hε
  refine ⟨Real.sqrt (|c| + (d + 1) * C ^ 2), ?_⟩
  intro M H _ _ _ _ j V A hA hskew v hv hcas hC i
  have h1 : ∀ k, inner ℂ (j v) (j (A k (A k v))) = -((‖j (A k v)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have h := hskew k v hv (A k v) (hA k v hv)
    rw [inner_self_eq_norm_sq_to_K] at h
    push_cast
    exact eq_neg_of_add_eq_zero_right h
  have h2 : (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re
      = -∑ k, ε k * ‖j (A k v)‖ ^ 2 := by

    rw [map_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_right, h1 k, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  rw [h2] at hcas
  have h3 : ∀ k, ε k = -1 → ‖j (A k v)‖ ^ 2 ≤ C ^ 2 * ‖j v‖ ^ 2 := by
    intro k hk
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC k hk) 2
  have hCN : 0 ≤ C ^ 2 * ‖j v‖ ^ 2 := by positivity
  have h4 : ∀ k, 0 ≤ ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2 := by
    intro k
    rcases hε k with hk | hk
    · rw [hk]; positivity
    · have := h3 k hk
      rw [hk]; linarith
  have h5 : ε i * ‖j (A i v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2
      ≤ ∑ k, (ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2) :=
    Finset.single_le_sum (f := fun k => ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2)
      (fun k _ => h4 k) (Finset.mem_univ i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h5
  have hc : c * ‖j v‖ ^ 2 ≤ |c| * ‖j v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
  have hc0 : 0 ≤ |c| * ‖j v‖ ^ 2 := by positivity
  have hd : 0 ≤ (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) := by positivity
  have h6 : ‖j (A i v)‖ ^ 2 ≤ (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2 := by
    have e : (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2
        = |c| * ‖j v‖ ^ 2 + (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) + C ^ 2 * ‖j v‖ ^ 2 := by ring
    rw [e]
    rcases hε i with hk | hk
    · rw [hk] at h5; linarith
    · have := h3 i hk
      linarith
  have h7 := Real.le_sqrt_of_sq_le h6
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] at h7
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.ReInnerGeOfSpanEigenvectors

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.re_inner_ge_of_span_eigenvectors :
    ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (T : Module.End ℂ M) (c : ℝ) (s : Set M), (∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (T x)) (j y) = inner ℂ (j x) (j (T y))) → (∀ x ∈ s, x ∈ V ∧ ∃ κ : ℂ, -c ≤ κ.re ∧ T x = κ • x) → ∀ v ∈ Submodule.span ℂ s, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (T v))).re := by
  intro M H _ _ _ _ j V T c s hsym hs v hv
  classical
  have hle : Submodule.span ℂ s ≤
      ⨆ κ : {κ : ℂ // -c ≤ κ.re}, (V ⊓ Module.End.eigenspace T (κ : ℂ)) := by
    refine Submodule.span_le.2 fun x hx => ?_
    obtain ⟨hxV, κ, hκ, hT⟩ := hs x hx
    exact Submodule.mem_iSup_of_mem (⟨κ, hκ⟩ : {κ : ℂ // -c ≤ κ.re})
      ⟨hxV, Module.End.mem_eigenspace_iff.2 hT⟩
  obtain ⟨f, hf, hfv⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 (hle hv)
  have hV : ∀ κ, f κ ∈ V := fun κ => (hf κ).1
  have hT : ∀ κ, T (f κ) = (κ : ℂ) • f κ := fun κ => Module.End.mem_eigenspace_iff.1 (hf κ).2
  have hrel : ∀ a b : {κ : ℂ // -c ≤ κ.re}, (starRingEnd ℂ) (a : ℂ) * inner ℂ (j (f a)) (j (f b))
      = (b : ℂ) * inner ℂ (j (f a)) (j (f b)) := by
    intro a b
    have := hsym _ (hV a) _ (hV b)
    rwa [hT, hT, map_smul, map_smul, inner_smul_left, inner_smul_right] at this
  have horth : ∀ a b, a ≠ b → inner ℂ (j (f a)) (j (f b)) = 0 := by
    intro a b hab
    by_cases h0 : j (f a) = 0
    · rw [h0, inner_zero_left]
    · have h1 : (starRingEnd ℂ) (a : ℂ) = a :=
        mul_right_cancel₀ (fun h => h0 (inner_self_eq_zero.1 h)) (hrel a a)
      have h2 := hrel a b
      rw [h1] at h2
      by_contra h3
      exact hab (Subtype.ext (mul_right_cancel₀ h3 h2))
  have hv' : v = ∑ a ∈ f.support, f a := hfv.symm
  have e1 : inner ℂ (j v) (j v) = ∑ a ∈ f.support, inner ℂ (j (f a)) (j (f a)) := by

    rw [hv', map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha]
    intro b _ hb
    exact horth a b hb.symm
  have e2 : inner ℂ (j v) (j (T v))
      = ∑ a ∈ f.support, (a : ℂ) * inner ℂ (j (f a)) (j (f a)) := by

    rw [hv', map_sum T, map_sum, map_sum, sum_inner]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [inner_sum, Finset.sum_eq_single_of_mem a ha, hT, map_smul, inner_smul_right]
    intro b _ hb
    rw [hT, map_smul, inner_smul_right, horth a b hb.symm, mul_zero]
  have hn : ∀ x : H, inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have e3 : ‖j v‖ ^ 2 = ∑ a ∈ f.support, ‖j (f a)‖ ^ 2 := by
    simp only [hn] at e1
    exact_mod_cast e1
  rw [e2, e3, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [hn, Complex.re_mul_ofReal]
  exact mul_le_mul_of_nonneg_right a.2 (sq_nonneg _)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.NearFinite

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.ConvolutionTheory.C.nearFinite :
    UpperTheory.ConvolutionTheory.C.NearFinite := by
  intro K _ _ n ι _ _ b ε hε horth U hU X _ _ _ τ c
  obtain ⟨B, hB, hsym, d, b', ε', hε', horth', hK⟩ := UpperTheory.exists_signed_basis_lieSubalgebra_exp_compact K n
  have hcas : casimir b ε = casimir b' ε' :=
    UpperTheory.casimir_eq_of_orthonormal_bases _ B ι (Fin d) b ε b' ε' hsym hε (fun i j => by rw [hB, horth])
      (fun i => by rcases hε' i with h | h <;> rw [h] <;> norm_num) horth'
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (normOneGL (K := K) (n := n)), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have hM : ∀ i, ∃ M : ℝ, ε' i = -1 → ∀ φ ∈ centralCuspForms K n,
      (∀ k, Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k)) φ = 0) →
      ‖cuspVecL μ ((gkModuleCusp K n).ρ (b' i) φ)‖ ≤ M * ‖cuspVecL μ φ‖ := by
    intro i
    by_cases hi : ε' i = -1
    · obtain ⟨M, hM⟩ := UpperTheory.norm_cuspVecL_gk_action_le_of_aeval_eq_zero K n μ (Module.finrank ℂ X) (fun k => LinearMap.charpoly (τ k)) (b' i)
        (fun k => ⟨(LinearMap.charpoly_monic _).ne_zero, (LinearMap.charpoly_natDegree _).le⟩) (hK i hi)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose M hM using hM
  obtain ⟨C', hC'⟩ := UpperTheory.norm_apply_le_of_laplacian_lower_bound d c (∑ i, |M i|) ε' hε'
  rw [hcas]
  suffices key : ∀ s : Set (cuspForms K n), (∀ φ ∈ s, φ ∈ centralCuspForms K n ∧
      (∀ u ∈ U, ∀ g, φ.1 (g * finEmb K n (u : AdelicGLn.integralFiniteGL K n)) = φ.1 g) ∧
      (∃ f : X →ₗ[ℂ] cuspForms K n, (∀ k x g, (f (τ k x)).1 g = (f x).1 (g * infEmb K n (k : archGroup K n))) ∧
        φ ∈ LinearMap.range f) ∧
      ∃ (h : φ.1 ∈ archSmooth K n) (κ : ℂ), -c ≤ κ.re ∧
        uAction (casimir b' ε') ⟨φ.1, h⟩ = κ • ⟨φ.1, h⟩) → FiniteDimensional ℂ (Submodule.span ℂ s) from
    key _ fun _ h => h
  intro s hs
  have hcent : Submodule.span ℂ s ≤ centralCuspForms K n := Submodule.span_le.2 fun φ hφ => (hs φ hφ).1
  have hskew : ∀ Y, ∀ x ∈ centralCuspForms K n, ∀ y ∈ centralCuspForms K n,
      inner ℂ (cuspVecL μ ((gkModuleCusp K n).ρ Y x)) (cuspVecL μ y) +
        inner ℂ (cuspVecL μ x) (cuspVecL μ ((gkModuleCusp K n).ρ Y y)) = 0 :=
    fun Y x hx y hy => petersson_inner_lieAlgebra_skewAdjoint μ Y hx hy
  have hT : ∀ φ : cuspForms K n, uActionCusp K n (casimir b' ε') φ =
      ∑ i, (ε' i : ℂ) • (gkModuleCusp K n).ρ (b' i) ((gkModuleCusp K n).ρ (b' i) φ) := by
    intro φ

    simp only [casimir, map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, gkModuleCusp_ρ_apply, Complex.coe_smul]
  have hsymT : ∀ x ∈ centralCuspForms K n, ∀ y ∈ centralCuspForms K n,
      inner ℂ (cuspVecL μ (uActionCusp K n (casimir b' ε') x)) (cuspVecL μ y) =
        inner ℂ (cuspVecL μ x) (cuspVecL μ (uActionCusp K n (casimir b' ε') y)) := by
    intro x hx y hy

    rw [hT, hT, map_sum, map_sum, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hskew (b' i) _ (ρ_mem_centralCuspForms (b' i) hx) y hy
    have h2 := hskew (b' i) x hx _ (ρ_mem_centralCuspForms (b' i) hy)
    rw [map_smul, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    linear_combination (ε' i : ℂ) * (h1 - h2)
  have hlow := UpperTheory.re_inner_ge_of_span_eigenvectors _ _ (cuspVecL μ) (centralCuspForms K n) (uActionCusp K n (casimir b' ε')) c s hsymT
    (fun x hx => by
      obtain ⟨h1, -, -, h, κ, hκ, he⟩ := hs x hx
      exact ⟨h1, κ, hκ, Subtype.ext (congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ)) he)⟩)
  have hpoly : ∀ k, ∀ φ ∈ Submodule.span ℂ s,
      Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k)) φ = 0 := by
    intro k
    have hle : Submodule.span ℂ s ≤
        LinearMap.ker (Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k))) := by
      refine Submodule.span_le.2 ?_
      intro φ hφ
      obtain ⟨-, -, ⟨f, hf, x, rfl⟩, -⟩ := hs φ hφ
      have h := map_aeval_apply_of_intertwine f (A := τ k) (B := (gkModuleCusp K n).σ k)
        (fun m => Subtype.ext (funext fun g => hf k m g)) (LinearMap.charpoly (τ k)) x
      rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at h
      exact h.symm
    exact fun φ hφ => hle hφ
  refine UpperTheory.finiteDimensional_cuspForms_of_level_and_derivOp_bound K n μ d b' C' U _ hU hcent (fun φ hφ u hu => ?_) (fun φ hφ => ?_)
  · have hle : Submodule.span ℂ s ≤ LinearMap.eqLocus
        (finRepCusp K n (u : AdelicGLn.integralFiniteGL K n)) LinearMap.id :=
      Submodule.span_le.2 fun ψ hψ => Subtype.ext (funext fun g => (hs ψ hψ).2.1 u hu g)
    exact hle hφ
  · refine hC' _ _ (cuspVecL μ) (centralCuspForms K n) (fun i => (gkModuleCusp K n).ρ (b' i))
      (fun i x hx => ρ_mem_centralCuspForms _ hx) (fun i => hskew (b' i)) φ (hcent hφ) ?_ fun i hi => ?_
    · rw [← hT]
      exact hlow φ hφ
    · refine (hM i hi φ (hcent hφ) fun k => hpoly k φ hφ).trans ?_
      refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (norm_nonneg _)
      exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
end
end
