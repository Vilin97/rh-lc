module

public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AddedBlockKernelSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdicNeighbourhood
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragedKernelSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragedVectorChoices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EqZeroOfIdealCompact
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteClassesPositiveSums
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelProperties
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussIndexIndependentOfChoice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussSumModulusOfLattice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermSumLattices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HenselRootsBounded
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HessianScalingIntegrals
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralLatticeRefinementIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelQuotientFinite
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelScalingBack
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanNormSquaredBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanPositiveSemidefinite
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModulusLocallyConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PadicChangeOfVariables
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PosSemidefEntryBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondVanishingOffRing
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubmoduleMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoBlockPoint
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CharacterOrthogonalityDual
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ColumnOperationTripleForm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelExplicitFormula
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramKernelHermitian

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteSumSwap

section

@[expose] public section

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.FiniteSumSwap

theorem finsum_swap {I J : Type} (P : I → Prop) [DecidablePred P] (T : J → Prop) [DecidablePred T]
    (hP : {q | P q}.Finite) (hT : {z | T z}.Finite) (a : ℂ) (g : J → ℂ) (F : J → I → ℂ)
    (e : I → ℂ) :
    ∑ᶠ q : I, (if P q then a * ∑ᶠ z : J, (if T z then g z * F z q else 0) else 0) * e q =
      a * ∑ᶠ z : J, (if T z then g z * ∑ᶠ q : I, (if P q then F z q else 0) * e q else 0) := by
  have h1 : ∀ f : I → ℂ, ∑ᶠ q : I, (if P q then f q else 0) * e q =
      ∑ q ∈ hP.toFinset, f q * e q := by
    intro f
    rw [finsum_eq_sum_of_support_subset (s := hP.toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [if_pos (by simpa using hq)]
    · intro q hq
      by_contra hq'
      have : ¬ P q := by simpa using hq'
      simp [this] at hq
  have h2 : ∀ f : J → ℂ, ∑ᶠ z : J, (if T z then f z else 0) = ∑ z ∈ hT.toFinset, f z := by
    intro f
    rw [finsum_eq_sum_of_support_subset (s := hT.toFinset)]
    · refine Finset.sum_congr rfl fun z hz => ?_
      rw [if_pos (by simpa using hz)]
    · intro z hz
      by_contra hz'
      have : ¬ T z := by simpa using hz'
      simp [this] at hz
  rw [h1, h2]
  simp_rw [h1, h2]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun q _ => ?_
  ring

end Formalism.FourierDecayAlt.P.FiniteSumSwap

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.FiniteSumSwap

theorem germExpansionKernelOfSteps : Formalism.FourierDecayAlt.A6.GermKernelAssemble := by
  intro hGerm hKp hInt hRoots K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨V, hV, H⟩ := hGerm K R ψ hD hn m hm γ hγ h Q hQ hQu
  refine ⟨V, hV, fun t c ht hc w' => ?_⟩
  have := hD.artin
  have := hD.red
  have hT : {z : Kˣ | z ^ (m + 1) = (-t) ^ m * c}.Finite :=
    hRoots K (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) ((-t) ^ m * c)
  have hP : {q : Cos R w' | IsInt R (orbZ w' (rep R q))}.Finite := hInt K R ψ hD w'
  rw [hKp K R ψ hD (pt2 h m t c) w']
  simp_rw [H t c ht hc]
  unfold germSum
  simp_rw [hKp K R ψ hD (addBlock h (m + 1) _) w']
  classical
  convert finsum_swap (fun q : Cos R w' => IsInt R (orbZ w' (rep R q)))
    (fun z : Kˣ => z ^ (m + 1) = (-t) ^ m * c) hP hT _ (germCoef R ψ m γ t)
    (fun z q => bbZ R ψ (addBlock h (m + 1) z) (orbZ w' (rep R q)))
    (fun q => conj (phase ψ (rep R q)))

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionOfSteps

section

@[expose] public section

noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

theorem germExpansionOfSteps : Formalism.FourierDecayAlt.A6.GermAssemble := by
  intro hHead hPhi K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨L₀, Λ₀, hL₀, hΛ₀, hΦ⟩ := hHead K R ψ hD hn m h Q hQ hQu
  obtain ⟨V, hV, hG⟩ := hPhi K R ψ hD hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQ hQu
  refine ⟨V, hV, fun t c ht hc n' Z' => ?_⟩
  obtain ⟨Φ, hyp, h1, h2⟩ := hΦ n' Z'
  rw [h1 t c, hG Φ hyp t c ht hc]
  congr 1
  funext z
  exact (h2 z).symm

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialMeansOrthogonal

section

@[expose] public section

open Formalism.FourierDecayAlt.A6

namespace Formalism.FourierDecayAlt.P

namespace A6x1

theorem norm_sq_sum_orth {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : Type}
    [Fintype A] (P : A → E) (e₁ : A → ℂ) (he : ∀ ρ, ‖e₁ ρ‖ = 1)
    (h : ∀ ρ ρ', ρ ≠ ρ' → inner ℂ (P ρ) (P ρ') = 0) :
    ‖∑ ρ, e₁ ρ • P ρ‖ ^ 2 = ∑ ρ, ‖P ρ‖ ^ 2 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_sum, Finset.sum_eq_single ρ]
  · rw [inner_self_eq_norm_sq (𝕜 := ℂ), norm_smul, he ρ, one_mul]
  · intro ρ' _ hne
    rw [inner_smul_left, inner_smul_right, h ρ ρ' (Ne.symm hne), mul_zero, mul_zero]
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ

end A6x1

theorem doubleMeanSplit : Formalism.FourierDecayAlt.A6.MeanSplit := by
  intro E _ _ A B _ _ u e₁ e₂
  rw [Fintype.sum_prod_type, mul_inv, mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_comm, Finset.smul_sum (r := e₁ ρ)]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul]

theorem partialMeansOrthogonal : Formalism.FourierDecayAlt.A6.POrth := by
  intro E _ _ A B _ _ u e₂ h ρ ρ' hne
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum]
  simp [h ρ ρ' _ _ hne]

theorem orthogonalMeanNorm : Formalism.FourierDecayAlt.A6.OrthNorm := by
  intro E _ _ A _ P e₁ he h
  rw [norm_smul, mul_pow, A6x1.norm_sq_sum_orth P e₁ he h, norm_inv, Complex.norm_natCast]

theorem averageBoundOfSteps : Formalism.FourierDecayAlt.A6.AvgBoundAssemble := by
  intro hM hP hO E _ _ A B _ _ u T e₁ e₂ hT he h
  rw [hM E A B u e₁ e₂]
  have h1 := hO E A (fun ρ => (Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)) e₁ he
    (hP E A B u e₂ h)
  have h2 := hT ((Fintype.card A : ℂ)⁻¹ •
    ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)))
  calc _ ≤ ‖(Fintype.card A : ℂ)⁻¹ •
        ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b))‖ ^ 2 := by
        gcongr
    _ = _ := by rw [h1]; ring

theorem averageBound : Formalism.FourierDecayAlt.A6.AvgBound :=
  averageBoundOfSteps doubleMeanSplit partialMeansOrthogonal orthogonalMeanNorm

end Formalism.FourierDecayAlt.P
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.RealPowerIdentities

section

@[expose] public section

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

namespace RealPowerIdentities

theorem inv_pow_triangle_mul_rpow_half {T : ℝ} (hT : 0 < T) (m : ℕ) :
    (T ^ (m * (m + 1) / 2))⁻¹ * T ^ ((m : ℝ) / 2) = T ^ (-((m : ℝ) ^ 2) / 2) := by
  have h2 : (2 : ℕ) ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  have hc : ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    push_cast
    ring
  rw [← Real.rpow_natCast, hc, ← Real.rpow_neg hT.le, ← Real.rpow_add hT]
  congr 1
  ring

theorem rpow_half_mul_pow_triangle {Z : ℝ} (hZ : 0 < Z) {m : ℕ} (hm : 1 ≤ m) :
    Z ^ ((m : ℝ) / 2) * Z ^ (m * (m - 1) / 2) = Z ^ ((m : ℝ) ^ 2 / 2) := by
  have h2 : (2 : ℕ) ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
  have hc : ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    push_cast [Nat.cast_sub hm]
    ring
  rw [← Real.rpow_natCast, hc, ← Real.rpow_add hZ]
  congr 1
  ring

end RealPowerIdentities

open RealPowerIdentities in
theorem germExpansionOfTestFunction : Formalism.FourierDecayAlt.A6.GermPhiAssemble := by
  intro hOsc hSt hInv hMod K _ _ _ R ψ hd hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  obtain ⟨L₁, Λ₁, hL₁, hΛ₁, V₁, hV₁, hO⟩ := hOsc K R ψ hd hn m hm L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  have hQ'c : IsCompact ((fun d : K => (-1) ^ m * d) '' Q) :=
    hQc.image (continuous_const.mul continuous_id)
  have hQ'u : ∀ d ∈ (fun d : K => (-1) ^ m * d) '' Q, IsUnit d := by
    rintro _ ⟨d, hdQ, rfl⟩
    exact (isUnit_one.neg.pow m).mul (hQu d hdQ)
  obtain ⟨V₂, hV₂, hS⟩ := hSt K R ψ hd hn m hm γ hγ L₁ Λ₁ _ hL₁ hΛ₁ hQ'c hQ'u
  refine ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂, ?_⟩
  intro Φ hΦ t c ht hc
  have hD : ((c * t ^ m : Kˣ) : K) ∈ Q := by simpa using hc
  obtain ⟨A, hA, hAz, hAo⟩ := hO Φ hΦ (c * t ^ m) hD
  obtain ⟨Λ, hΛ, hinv⟩ := hInv K R ψ hd hn m L₁ Λ₁ hL₁ hΛ₁ A ((t⁻¹ : Kˣ) : K)
    (((-1) ^ m * (c * t ^ m) : Kˣ) : K) hA
  have hD' : (((-1) ^ m * (c * t ^ m) : Kˣ) : K) ∈ (fun d : K => (-1) ^ m * d) '' Q :=
    ⟨_, hD, by simp⟩
  have hDeq : ((-1) ^ m * (c * t ^ m) : Kˣ) = (-t) ^ m * c := by
    rw [neg_pow t m]
    ac_rfl
  have hT : 0 < modK R (t : K) := (hMod K R ψ hd t t).1
  rw [hAo t c ht.1 rfl Λ hΛ hinv, hS t _ A ht.2 hD' hA Λ hΛ hinv]
  unfold germSum
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_pow_triangle_mul_rpow_half hT m]
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : z ^ (m + 1) = (-1) ^ m * (c * t ^ m)
  · have hZ : 0 < modK R (z : K) := (hMod K R ψ hd z z).1
    rw [if_pos hz, if_pos (hz.trans hDeq), hAz z hz]
    unfold germCoef
    rw [← rpow_half_mul_pow_triangle hZ hm]
    push_cast
    ring
  · rw [if_neg hz, if_neg (fun h => hz (h.trans hDeq.symm))]

end Formalism.FourierDecayAlt.P
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionMatrixFunction

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6

theorem gauss_hessian_index_exists : Formalism.FourierDecayAlt.A6.GaussHess :=
  gauss_hessian_index_of_parts gauss_sum_modulus_of_lattice gauss_index_independent_of_choice
    phase_hessian_determinant modulus_positive_multiplicative volume_scaling_identity

theorem padic_stationary_phase : Formalism.FourierDecayAlt.A6.StationaryPhase :=
  stationaryPhaseOfSteps nonStationary morseLemma integral_field_refinement
    modulus_positive_multiplicative rootsFinite compactOpenChoice orthogonal_lattice_properties
    modulusLocallyConstant oscillatory_integral_invariant volume_scaling_identity rootsSeparated
    smallModules admissible_gauss_sum_small lattice_family_finite

theorem germ_expansion_matrix_function : Formalism.FourierDecayAlt.A6.GermPhi :=
  germExpansionOfTestFunction orbital_integral_change_of_variables padic_stationary_phase
    oscillatory_integral_invariant modulus_positive_multiplicative

theorem germ_expansion_with_head : Formalism.FourierDecayAlt.A6.Germ :=
  germExpansionOfSteps head_reduction_lemma germ_expansion_matrix_function

theorem germ_kernel_expansion : Formalism.FourierDecayAlt.A6.GermKernel :=
  germExpansionKernelOfSteps germ_expansion_with_head kernel_as_coset_sum integral_points_finite
    rootsFinite

theorem germ_identity_bis : Formalism.FourierDecayAlt.A6.GermIdentity :=
  germIdentityOfSteps gauss_hessian_index_exists germ_kernel_expansion gramKernelHermitian
    second_vanishing_off_ring modulus_positive_multiplicative rootsFinite shiftUnit_statement
    shiftSmall_statement rootCutStable rootCorrection square_near_unit phase_difference_estimate
    phase_locally_constant modulusLocallyConstant integral_lattice_refinement_identity
    padic_change_of_variables crossTermsVanish

theorem theta_omega_bound : Formalism.FourierDecayAlt.A6.ThOm :=
  thetaOnDomainOfSteps germ_identity_bis averaged_vector_choices_exist phase_locally_constant
    gramKernelHermitian modulusLocallyConstant compactOpenChoice lattice_family_finite
    shiftUnit_statement smallUnits gram_equality_of_vectors averaged_vector_norm_bound
    cut_posSemidef heads_distinct_determinant_orthogonal head_size_add_block
    modulus_positive_multiplicative kernel_gram_property kernel_block_diagonal_by_modulus
    gramRealisation averageBound parsevalGroup_statement annihilatorCharacters
    orthogonal_lattice_properties characterMean truncated_average_norm_formula thetaAverageLower
    averaged_kernel_periodic_psd averaged_kernel_parseval

theorem lattice_average_induction : Formalism.FourierDecayAlt.A5.ThetaExistsStep :=
  thetaExistsStepOfSteps theta_omega_bound finite_family_truncation_module
    added_block_kernel_support head_size_one_in_GL rootStableExhaustion lattice_family_finite
    posSemidefEntryBound posSemidefClosed boundedSubsequence

theorem lattice_average_lemma_full : Formalism.FourierDecayAlt.A5.LemmaA :=
  lattice_average_lemma_from_parts second_gram_and_vanishing first_kernel_parseval
    first_theta_kernel_equality first_theta_equals_first_kernel lattice_average_induction
    zero_kernel_all_ones added_block_kernel_support added_block_kernel_block_diagonal

end Formalism.FourierDecayAlt.P
end
end
