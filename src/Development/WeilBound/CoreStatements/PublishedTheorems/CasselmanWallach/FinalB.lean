module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CwOf
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisFormSumOfGain
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisSumOfOrthogonality
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirPowerCommute
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirRealOfCentral
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirRealScalar
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ColumnMomentsOfSymmetric
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CommutatorAdjointHolds
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
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenWeightedSumBound
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenbasisOfBasic
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonalOfCalculus
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EnvelopingAlgebraGrowthBound
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusOfBasic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GroupFactsHolds
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GrowthOfBasic
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GrowthPolynomialOperator
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.IdentityFiltrationBound
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Lemma
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KFiniteInclusion
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionSingle
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MaximumPrincipleOfFacts
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.NilpotentOfPowerTraces
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.OrthonormalEigenbasisOfBasic
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PMaxPr
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SecondDerivativeHolds
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.U0Commute
public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.WordFiltrationCommute

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CompactGroupFacts

section

@[expose] public section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS Filter Topology Set

namespace PositivityTheory.CW

theorem second_derivative_holds : B3 := by
  intro ψ ψ' d hmax hψ hd
  by_contra hneg
  have hdpos : 0 < d := lt_of_not_ge hneg
  have h0 : ψ' 0 = 0 := hmax.hasDerivAt_eq_zero (hψ 0)
  have hslope := hd.tendsto_slope_zero_right
  have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t ≤ ψ 0 := nhdsWithin_le_nhds hmax
  have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (ψ' (0 + t) - ψ' 0) := hslope (lt_mem_nhds hdpos)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)
  have hu0 : (0 : ℝ) < u := hu
  have hb : u / 2 ∈ Set.Ioo (0 : ℝ) u := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' (half_pos hu0)
    (fun t _ => (hψ t).continuousAt.continuousWithinAt) (fun t _ => hψ t)
  have hcu : c ∈ Set.Ioo (0 : ℝ) u := ⟨hc.1, hc.2.trans (by linarith)⟩
  obtain ⟨-, hc'⟩ := hsub hcu
  obtain ⟨hbmax, -⟩ := hsub hb
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hc'
  have hψc : 0 < ψ' c := (pos_iff_pos_of_mul_pos hc').mp (inv_pos.mpr hc.1)
  rw [hcslope, sub_zero] at hψc
  have hdiff : 0 < ψ (u / 2) - ψ 0 := by
    have := mul_pos hψc (half_pos hu0)
    rwa [div_mul_cancel₀ _ (half_pos hu0).ne'] at this
  linarith

end PositivityTheory.CW

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GelfandCentralHolds

section

@[expose] public section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirPowerCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem comm_pow (E : Fin n → Fin n → Module.End ℂ V) (hE : IsGlRep E) (c d : Fin n) :
    ∀ (k : ℕ) (a b : Fin n), E c d * (Mm E ^ k) a b - (Mm E ^ k) a b * E c d =
      (if d = a then (Mm E ^ k) c b else 0) - (if b = c then (Mm E ^ k) a d else 0) := by
  have hM : ∀ i j, Mm E i j = E i j := fun _ _ => rfl
  intro k
  induction k with
  | zero =>
    intro a b
    simp only [pow_zero, Matrix.one_apply]
    have h0 : (if d = a then (if c = b then (1 : Module.End ℂ V) else 0) else 0) =
        (if b = c then (if a = d then 1 else 0) else 0) := by
      by_cases h2 : d = a
      · subst h2
        by_cases h3 : b = c
        · subst h3; simp
        · simp [h3, Ne.symm h3]
      · simp [h2, Ne.symm h2]
    rw [h0, sub_self]
    split_ifs <;> simp
  | succ k ih =>
    intro a b
    have key : ∀ j, E c d * ((Mm E ^ k) a j * E j b) - ((Mm E ^ k) a j * E j b) * E c d
        = (E c d * (Mm E ^ k) a j - (Mm E ^ k) a j * E c d) * E j b
          + (Mm E ^ k) a j * (E c d * E j b - E j b * E c d) := by
      intro j; noncomm_ring
    simp only [pow_succ, Matrix.mul_apply, hM]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [key, ih, hE c d]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h1 : d = a <;> by_cases h2 : b = c <;> simp [h1, h2] <;> abel

end CasimirPowerCommute

theorem gelfand_central_holds : A2 := by
  intro n ε V _ _ E h k c d
  have hc := CasimirPowerCommute.comm_pow E h.gl c d k
  rw [← sub_eq_zero, Matrix.trace, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [Matrix.diag_apply, hc, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self]

end PositivityTheory.CW

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.InversePowerBoundHolds

section

@[expose] public section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace InversePowerBound

lemma sq_le_inv_pow (s : ℕ) (y : ℝ) (hy : -1 < y) (h0 : 0 ≤ 1 - (s : ℝ) * y / 2) :
    (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((1 + y) ^ s)⁻¹ := by
  have h1 : 0 < 1 + y := by linarith
  have hpos : 0 < (1 + y) ^ s := pow_pos h1 s

  have hA : 1 - (s : ℝ) * y / 2 ≤ Real.exp (-((s : ℝ) * y / 2)) := by
    linarith [Real.add_one_le_exp (-((s : ℝ) * y / 2))]
  have hB : (1 + y) ^ s ≤ Real.exp ((s : ℝ) * y) := by
    calc (1 + y) ^ s ≤ (Real.exp y) ^ s :=
          pow_le_pow_left₀ h1.le (by linarith [Real.add_one_le_exp y]) s
      _ = Real.exp ((s : ℝ) * y) := by rw [← Real.exp_nat_mul]
  have hC : (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y)) := by
    calc (1 - (s : ℝ) * y / 2) ^ 2 ≤ (Real.exp (-((s : ℝ) * y / 2))) ^ 2 :=
          pow_le_pow_left₀ h0 hA 2
      _ = Real.exp (-((s : ℝ) * y)) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc (1 - (s : ℝ) * y / 2) ^ 2 ≤ Real.exp (-((s : ℝ) * y)) := hC
    _ = (Real.exp ((s : ℝ) * y))⁻¹ := by rw [Real.exp_neg]
    _ ≤ ((1 + y) ^ s)⁻¹ := inv_anti₀ hpos hB

end InversePowerBound

theorem inverse_power_bound_holds : A10 := by
  intro s _hs
  refine ⟨(s : ℝ) ^ 4 / 16, by positivity, fun y hy => ?_⟩
  have hpos : 0 < ((1 + y) ^ s)⁻¹ := inv_pos.mpr (pow_pos (by linarith) s)

  have hsq : 1 - (s : ℝ) * y + (s : ℝ) ^ 2 / 4 * y ^ 2 = (1 - (s : ℝ) * y / 2) ^ 2 := by ring
  have e : (s : ℝ) ^ 4 / 16 * y ^ 4 = ((s : ℝ) * y / 2) ^ 4 := by ring
  by_cases h0 : 0 ≤ 1 - (s : ℝ) * y / 2
  · have h := InversePowerBound.sq_le_inv_pow s y hy h0
    have : 0 ≤ (s : ℝ) ^ 4 / 16 * y ^ 4 := by positivity
    linarith
  ·
    rw [not_le] at h0
    have hu : 1 < (s : ℝ) * y / 2 := by linarith
    have k1 : (1 - (s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
    have k2 : ((s : ℝ) * y / 2) ^ 2 ≤ ((s : ℝ) * y / 2) ^ 4 := by
      have : 1 ≤ ((s : ℝ) * y / 2) ^ 2 := by nlinarith
      nlinarith
    linarith

end PositivityTheory.CW

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SymmetricPowerHolds

section

@[expose] public section

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace identity_filtration_of_scalar

theorem symm_pow {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (P : Module.End ℂ W)
    (hP : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) :
    ∀ k : ℕ, ∀ x y, inner ℂ ((P ^ k) x) y = inner ℂ x ((P ^ k) y) := by
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hP]
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, (Commute.self_pow P k).eq]

end identity_filtration_of_scalar

theorem symmetric_power_holds : A7 := by
  intro W _ _ P hP x hx h0 j
  induction j with
  | zero => simp
  | succ j ih =>
    have hsym := identity_filtration_of_scalar.symm_pow P hP (2 ^ j)

    have key : (inner ℂ x ((P ^ (2 ^ (j + 1))) x)).re = ‖(P ^ (2 ^ j)) x‖ ^ 2 := by
      rw [pow_succ, pow_mul, sq, Module.End.mul_apply, ← hsym]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) ((P ^ (2 ^ j)) x)

    have cs : |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ≤ ‖(P ^ (2 ^ j)) x‖ := by
      calc _ ≤ ‖inner ℂ x ((P ^ (2 ^ j)) x)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖(P ^ (2 ^ j)) x‖ := norm_inner_le_norm _ _
        _ = _ := by rw [hx, one_mul]
    have hpos : 0 ≤ (inner ℂ x (P x)).re ^ (2 ^ j) := pow_nonneg h0 _
    calc (inner ℂ x (P x)).re ^ (2 ^ (j + 1)) = ((inner ℂ x (P x)).re ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
      _ ≤ ((inner ℂ x ((P ^ (2 ^ j)) x)).re) ^ 2 := pow_le_pow_left₀ hpos ih 2
      _ = |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖(P ^ (2 ^ j)) x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) cs 2
      _ = _ := key.symm

end PositivityTheory.CW

end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EtaleCohomologyNegativeVanishingDegreeZero

section

@[expose] public section

namespace PositivityTheory.CWB

open PositivityTheory.CW

theorem word_filtration_basic : A0 := orthonormal_eigenbasis_of_basic

theorem aux_statement_7 : A1 := word_filtration_of_length

theorem filtration_adjoint_stable : FiltrationAdjointStable := adjoint_stable_filtration

theorem gelfand_invariants_central : A2 := gelfand_central_holds

theorem casimir_eigenvector_exists : A3 := casimir_eigen_exists

theorem casimir_real_scalar : CasimirIsRealScalar := casimir_real_of_central gelfand_invariants_central casimir_eigenvector_exists

theorem power_traces_nilpotent : A4 := nilpotent_of_power_traces

theorem commutator_adjoint_lower_order : CommutatorAdjointModLower := commutator_adjoint_holds aux_statement_7

theorem aux_statement_6 : A5 := normal_nilpotent_of_commutator aux_statement_7 gelfand_invariants_central casimir_eigenvector_exists power_traces_nilpotent commutator_adjoint_lower_order

theorem identity_operator_filtration : A6 := SymmetricPowerMatrix word_filtration_basic aux_statement_7 casimir_real_scalar

theorem matrix_symmetric_power : A7 := symmetric_power_holds

theorem column_moments_bound : ColumnOperatorMoments := column_moments_of_symmetric matrix_symmetric_power

theorem second_moment_bound : A8 := second_moment_of_columns word_filtration_basic aux_statement_7 filtration_adjoint_stable casimir_real_scalar aux_statement_6 identity_operator_filtration column_moments_bound

theorem etale_cohomology_vanishing_negative_degree_zero : A9 := a9_of_a0_a1_eigenbasis_a6 word_filtration_basic aux_statement_7 casimir_real_scalar identity_operator_filtration

theorem inverse_power_square_bound : A10 := inverse_power_bound_holds

theorem orthonormal_eigenbasis_exists : EigenbasisExists := eigenbasis_of_basic word_filtration_basic

theorem functional_calculus : FunctionalCalculusLaws := functional_calculus_of_basic word_filtration_basic

theorem normal_nilpotent_graded_zero : EigenspacesOrthogonalAlt := eigenspaces_orthogonal_of_calculus word_filtration_basic functional_calculus

theorem eigen_gain_high : A12 := eigen_gain_of_moments word_filtration_basic second_moment_bound etale_cohomology_vanishing_negative_degree_zero inverse_power_square_bound functional_calculus

theorem basis_sum_form_values : BasisSumAsFormValues := basis_sum_of_orthogonality word_filtration_basic functional_calculus normal_nilpotent_graded_zero

theorem eigenspace_form_sum : A13 := basis_form_sum_of_gain word_filtration_basic functional_calculus eigen_gain_high basis_sum_form_values

theorem word_length_filtration : B1 := growth_of_basic word_filtration_basic

theorem hilbert_schmidt_growth : B2 := heightFunctionalStatement_of_pairingProperties

theorem tateTwist_local_to_global_strictlyHenselian : B3 := second_derivative_holds

theorem group_facts : UnitaryGroupFacts := group_facts_holds

theorem maximum_principle_one_function : MaximumPrincipleVar := maximum_principle_of_facts hilbert_schmidt_growth tateTwist_local_to_global_strictlyHenselian group_facts

theorem second_derivative_sum_squares : SumSquaresSecondDerivative := second_derivatives_of_growth word_length_filtration group_facts

theorem lieExponentialMajorant_holds : B5 := eigen_weighted_sum_bound word_filtration_basic functional_calculus

theorem maxPr : MaxPr := maxPr_of casimir_real_scalar orthonormal_eigenbasis_exists eigenspace_form_sum group_facts maximum_principle_one_function second_derivative_sum_squares lieExponentialMajorant_holds

end PositivityTheory.CWB
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FinalB

section

@[expose] public section

namespace PositivityTheory.CWB

theorem casselmanWallach : GlobalTheory.Published.CasselmanWallach :=
  PositivityTheory.CW.cw_of maxPr

end PositivityTheory.CWB
end
end
