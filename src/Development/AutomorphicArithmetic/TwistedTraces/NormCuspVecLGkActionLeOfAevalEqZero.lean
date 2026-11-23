module

public import GroundTheory.AutomorphicForms.L2LocalComponents.CuspSmooth
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Ring.Basic
public import Development.AutomorphicArithmetic.TwistedTraces.NormDerivOrbitLeOfPolynomialAnnihilated
import GroundTheory.AutomorphicForms.DixmierMalliavinBasic
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.ExistsBoundOfIsRootExpMulForall

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_bound_of_isRoot_exp_mul_forall :
    ∀ (d : ℕ) (p : ℝ → ℂ[X]), (∀ t, p t ≠ 0 ∧ (p t).natDegree ≤ d) → ∃ M : ℝ, ∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M := by
  intro d p hp
  classical
  have hfin : Set.Finite {z : ℂ | ∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))} := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (d + 1)
    obtain ⟨R, hR⟩ := (F.finite_toSet.isBounded).exists_norm_le
    set S : ℝ := |R| + 1 with hS
    have hSpos : 0 < S := by positivity
    have hRS : ∀ z ∈ F, ‖z‖ ≤ S := fun z hz => by
      have h1 := hR z (Finset.mem_coe.mpr hz)
      have h2 := le_abs_self R
      linarith
    set t : ℝ := S⁻¹ with ht
    have htpos : 0 < t := inv_pos.mpr hSpos
    have hn : ∀ z ∈ F, ‖z * (t : ℂ)‖ ≤ 1 := fun z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht]
      rw [mul_inv_le_iff₀ hSpos, one_mul]
      exact hRS z hz
    have hinj : Set.InjOn (fun z : ℂ => Complex.exp (z * (t : ℂ))) F := by
      intro z hz w hw h
      obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
      have h1 := hn z hz
      have h2 := hn w hw
      have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ ≤ 2 := by
        have : (n : ℂ) * (2 * Real.pi * Complex.I) = z * t - w * t := by rw [hn']; ring
        rw [this]
        have := norm_sub_le (z * (t : ℂ)) (w * t)
        linarith
      have hn0 : n = 0 := by
        by_contra hne
        have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
        have h5 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
          simp [abs_of_pos Real.pi_pos]
        have h6 := Real.pi_gt_three
        rw [h5] at h3
        nlinarith
      rw [hn0] at hn'
      have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
      have : z * (t : ℂ) = w * t := by simpa using hn'
      exact mul_right_cancel₀ htne this
    have hsub : (F.image (fun z : ℂ => Complex.exp (z * (t : ℂ)))).val ⊆ (p t).roots := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hx)
      exact (Polynomial.mem_roots (hp t).1).mpr (hF (Finset.mem_coe.mpr hz) t)
    have hle := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_image_of_injOn hinj, hcard] at hle
    have := (hp t).2
    omega
  obtain ⟨M, hM⟩ := hfin.isBounded.exists_norm_le
  exact ⟨M, fun z hz => hM z hz⟩
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.NormCuspVecLGkActionLeOfAevalEqZero

section

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

private theorem pow_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (k : archCompact K n) (m : ℕ) :
    ∀ φ ∈ centralCuspForms K n, (archRepT μ (k : archGroup K n) ^ m) (cuspVecL μ φ) =
      cuspVecL μ (((gkModuleCusp K n).σ k ^ m) φ) := by
  induction m with
  | zero =>
    intro φ _
    simp
  | succ m ih =>
    intro φ hφ
    rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, Module.End.mul_apply, ← cuspToL2_sigma μ k hφ,
      ih _ (σ_mem_centralCuspForms k hφ)]

private theorem aeval_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (k : archCompact K n) (q : ℂ[X]) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) :
    aeval (archRepT μ (k : archGroup K n)) q (cuspVecL μ φ) =
      cuspVecL μ (aeval ((gkModuleCusp K n).σ k) q φ) := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [map_add (f := _), ContinuousLinearMap.add_apply, LinearMap.add_apply, ha, hb]
  | monomial m c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, ContinuousLinearMap.mul_apply,
      pow_cuspVecL μ k m φ hφ]
    simp [Algebra.algebraMap_eq_smul_one]

theorem UpperTheory.norm_cuspVecL_gk_action_le_of_aeval_eq_zero :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (d : ℕ) (p : archCompact K n → ℂ[X]) (Y : (isExpLieAlgebra K n).lieSubalgebra), (∀ k, p k ≠ 0 ∧ (p k).natDegree ≤ d) → (∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y) ∈ archCompact K n) → ∃ M : ℝ, ∀ φ ∈ centralCuspForms K n, (∀ k, aeval ((gkModuleCusp K n).σ k) (p k) φ = 0) → ‖cuspVecL μ ((gkModuleCusp K n).ρ Y φ)‖ ≤ M * ‖cuspVecL μ φ‖ := by
  intro K _ _ n μ _ d p Y hp hk
  let kk : ℝ → archCompact K n := fun t => ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y), hk t⟩
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_isRoot_exp_mul_forall d (fun t => p (kk t)) (fun t => hp _)
  refine ⟨M, fun φ hφ hkill => ?_⟩
  have hy := (isExpLieAlgebra K n).hasDerivAt_derivOp (archRepT μ) (isSmoothVector_cuspToL2 μ hφ)
    ((isExpLieAlgebra K n).ofLie Y)
  have e := derivOp_cuspVecL μ hφ ((isExpLieAlgebra K n).ofLie Y)
  rw [IsExpLieAlgebra.toLie_ofLie] at e
  rw [e] at hy
  have hu : ∀ t : ℝ, (archRepT μ ((kk t : archCompact K n) : archGroup K n)) =
      archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) := fun t => rfl
  refine UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated (CuspL2 μ)
    (fun t => archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)))
    (fun t => p (kk t)) M (cuspVecL μ φ) _ ?_ ?_ ?_ ?_ hy ?_ hM
  · ext1 x
    simp [(isExpLieAlgebra K n).expG_zero]
  · intro s t
    ext1 x
    rw [(isExpLieAlgebra K n).expG_add_smul, BanachRep.map_mul_apply]
    rfl
  · intro t x
    rw [archRepT_apply]
    exact UnitaryRep.norm_map _ _ _
  · have hfin := (gkModuleCusp K n).locallyFinite φ
    have hle : Submodule.span ℂ (Set.range fun t : ℝ =>
        archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) (cuspVecL μ φ)) ≤
        (Submodule.span ℂ (Set.range fun k => (gkModuleCusp K n).σ k φ)).map (cuspVecL μ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨kk t, rfl⟩, cuspToL2_sigma μ (kk t) hφ⟩
    exact Submodule.finiteDimensional_of_le hle
  · intro t
    have := aeval_cuspVecL μ (kk t) (p (kk t)) hφ
    rw [hkill, map_zero] at this
    exact this
end
end
