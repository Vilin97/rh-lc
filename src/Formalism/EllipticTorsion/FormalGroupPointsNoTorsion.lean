module

public import Formalism.EllipticTorsion.UnitCancel
public import Formalism.EllipticTorsion.ChangeIntegral
public import Formalism.EllipticTorsion.CoeffRing
public import Formalism.EllipticTorsion.CompExpWeight
public import Formalism.EllipticTorsion.EllipticTorsionWeights
public import Formalism.EllipticTorsion.FormalGroupPointsParametrisation
public import Formalism.EllipticTorsion.IsoExpand
public import Formalism.EllipticTorsion.VeluIntegralModel
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Change
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CoefficientWeightsLemmaTwo
import Formalism.EllipticTorsion.EllipticTorsionProofs.CompExp
import Formalism.EllipticTorsion.EllipticTorsionProofs.ConstantCoeffLogOnePlus
import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeThree
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeTwo
import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsHomDef
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsParamDef
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsSubgroupHolds
public import Formalism.EllipticTorsion.Statement
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.Linter.Style
public import Mathlib.Topology.Algebra.Polynomial
public import Formalism.EllipticTorsion.EllipticTorsionProofs.IntegralPSBserSubOne
public import Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion
import Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre
public import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant
public import Formalism.EllipticTorsion.EllipticTorsionProofs.LogWeight
import Formalism.EllipticTorsion.Statement
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv
public import Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt
import Formalism.EllipticTorsion.UnitCancel
import Formalism.EllipticTorsion.EllipticTorsionProofs.IntegralPSBserSubOne
public import Formalism.EllipticTorsion.EllipticTorsionProofs.VeluInt
public import Formalism.EllipticTorsion.EllipticTorsionProofs.VeluUSeries
import Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst

-- Source module: Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsSumPowPrimePow

section

@[expose] public section

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

namespace FrobeniusExpansion

theorem exists_sum_pow_prime_pow {A : Type*} [CommRing A] {ι : Type*} [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) (s : Finset ι) (f : ι → A) (n : ℕ) :
    ∃ r : A, (∑ i ∈ s, f i) ^ (p ^ n) = ∑ i ∈ s, f i ^ (p ^ n) + (p : A) * r := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp [zero_pow (pow_ne_zero n hp.ne_zero)]
  | insert a s ha ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := exists_add_pow_prime_pow_eq hp (f a) (∑ i ∈ s, f i) n
    refine ⟨f a * (∑ i ∈ s, f i) * r' + r, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr', hr]
    ring

end FrobeniusExpansion

open MvPolynomial in
theorem frobenius_expansion : FrobExpand := by
  intro K _ _ p hp _hp1 m j a b ha hab α
  classical
  set R := unitBall K
  let a' : Fin m → R := fun e => ⟨a e, ha e⟩
  obtain ⟨r, hr⟩ := FrobeniusExpansion.exists_sum_pow_prime_pow (A := MvPolynomial (Fin m) R) hp
    Finset.univ (fun e => C (a' e) * X e) j
  have hmap : (∑ e, C (a e) * X e : MvPolynomial (Fin m) K)
      = map R.subtype (∑ e, C (a' e) * X e) := by
    simp [a']
  have key : (∑ e, C (a e) * X e : MvPolynomial (Fin m) K) ^ (p ^ j)
        - ∑ e, C (b e) * X e ^ (p ^ j)
      = ∑ e, C (a e ^ (p ^ j) - b e) * X e ^ (p ^ j)
        + C (p : K) * map R.subtype r := by

    rw [hmap, ← map_pow, hr, map_add (f := _), map_sum, map_mul, map_natCast]
    simp only [map_pow, map_mul, map_C, map_X, mul_pow, map_sub, sub_mul,
      Finset.sum_sub_distrib, map_natCast]
    simp [a']
    ring
  rw [key, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sum, coeff_C_mul, coeff_map]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun e _ => ?_
    rw [coeff_C_mul, coeff_X_pow, norm_mul]
    split_ifs
    · simpa using hab e
    · simp
  · rw [norm_mul]
    have h1 : ‖(r.coeff α : K)‖ ≤ 1 := (r.coeff α).2
    calc ‖(p : K)‖ * ‖(r.coeff α : K)‖ ≤ ‖(p : K)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖(p : K)‖ := mul_one _

end Formalism.ELL
end
end
end

-- Source module: Formalism.EllipticTorsion.EllipticTorsionProofs.IntVal

section

@[expose] public section

noncomputable section

namespace Formalism.ELL.IntegerValuedContinuity

theorem continuous_eval {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] (P : Polynomial K) :
    Continuous fun b : ℤ_[p] => P.eval (algebraMap ℚ_[p] K (b : ℚ_[p])) := by
  have h1 : Continuous (algebraMap ℚ_[p] K) := by
    have : (⇑(algebraMap ℚ_[p] K)) = fun c => c • (1 : K) := by
      funext c; exact Algebra.algebraMap_eq_smul_one c
    rw [this]; exact continuous_id.smul continuous_const
  have h2 : Continuous (fun b : ℤ_[p] => (b : ℚ_[p])) := continuous_subtype_val
  exact (P.continuous).comp (h1.comp h2)

end Formalism.ELL.IntegerValuedContinuity

namespace Formalism.ELL

theorem integer_valued_padic_integers : IntValuedZp := by
  intro p _ K _ _ P hP b
  have hc := Formalism.ELL.IntegerValuedContinuity.continuous_eval (p := p) (K := K) P
  have hclosed : IsClosed {b : ℤ_[p] | ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1} :=
    isClosed_le (continuous_norm.comp hc) continuous_const
  refine PadicInt.denseRange_natCast.induction_on b hclosed ?_
  intro n
  show ‖P.eval (algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]))‖ ≤ 1
  have : algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]) = (n : K) := by
    simp
  rw [this]; exact hP n

end Formalism.ELL
end
end
end

-- Source module: Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf

section

section

universe u

namespace Formalism.ELL.unitAtAlt

open Formalism.ELL

lemma two_or_three {K : Type u} [NormedField K] [IsUltrametricDist K] :
    ‖(2 : K)‖ = 1 ∨ ‖(3 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have h3 : ‖(3 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 3
  have h1 : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
    have : (1 : K) = 3 + -2 := by norm_num
    rw [this]
    simpa [norm_neg] using IsUltrametricDist.norm_add_le_max (3 : K) (-2)
  rw [norm_one] at h1
  by_cases h : ‖(2 : K)‖ = 1
  · exact Or.inl h
  · right
    have hlt : ‖(2 : K)‖ < 1 := lt_of_le_of_ne h2 h
    rcases le_max_iff.mp h1 with h' | h'
    · exact le_antisymm h3 h'
    · exact absurd h' (not_le.mpr hlt)

lemma of_model {K : Type u} [NormedField K] (W : WeierstrassCurve K) (j : K)
    (hI : IntegralModel W) (hc : W.c₄ ^ 3 = j * W.Δ) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j := by
  have hne : W.Δ ≠ 0 := by
    intro h; rw [h, norm_zero] at hΔ; exact zero_ne_one hΔ
  have : W.IsElliptic := ⟨hne.isUnit⟩
  refine ⟨W, inferInstance, hI, hΔ, ?_⟩
  rw [WeierstrassCurve.j, hc, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  field_simp

end Formalism.ELL.unitAtAlt

namespace Formalism.ELL

open Formalism.ELL.unitAtAlt

theorem modelUnit_of (hL : Formalism.ELL.ModelLegendre.{u}) (hD : Formalism.ELL.ModelDeuring.{u}) :
    Formalism.ELL.ModelUnit.{u} := by
  intro K _ _ _ j hj
  rcases two_or_three (K := K) with h2 | h3
  · obtain ⟨l, hl, _hl1, hc, hΔ⟩ := hL K h2 j hj
    refine of_model (legendre l) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [legendre]
    · simp
    · rw [norm_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      simp [hl]
    · simp
    · exact hl.le
    · simp
  · obtain ⟨a, ha, hc, hΔ⟩ := hD K h3 j hj
    refine of_model (deuring a) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [deuring]
    · exact ha
    all_goals simp

end Formalism.ELL
end
end

-- Source module: Formalism.EllipticTorsion.EllipticTorsionProofs.UnitCancel

section

section

universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

theorem unit_cancellation : Formalism.ELL.UnitCancel.{u} := by
  intro p _ K _ _ _ _ σ G b hb h
  obtain ⟨u, rfl⟩ := hb
  have := Formalism.ELL.N_padic_integer_smul p K σ _ h ((u⁻¹ : (ℤ_[p])ˣ) : ℤ_[p])
  convert this using 1
  rw [smul_smul, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, inv_mul_cancel]
  simp

end Formalism.ELL
end
end
end

-- Source module: Formalism.EllipticTorsion.FormalGroupPointsNoTorsion

section

@[expose] public section

universe u

namespace Formalism.ELL

theorem legendreInv : LegendreInv.{u} := legendre_invariant
theorem deuringInv : DeuringInv.{u} := deuring_invariant
theorem modelLegendre : ModelLegendre.{u} := legendre_model
theorem modelDeuring : ModelDeuring.{u} := deuring_model
theorem modelUnit : ModelUnit.{u} := by
  apply modelUnit_of <;> first | exact modelLegendre | exact modelDeuring | exact legendreInv | exact deuringInv
theorem intValuedZp : IntValuedZp.{u} := integer_valued_padic_integers
theorem nAddSubgroup : NAddSubgroup.{u} := N_additive_subgroup
theorem nZpSmul : NZpSmul.{u} := N_padic_integer_smul
theorem nPderiv : NPderiv.{u} := N_partial_derivative

theorem formal_group_points_subgroup : FormalGroupPointsSubgroup'.{u} := formal_group_points_subgroup_holds
theorem formal_group_points_no_torsion : FormalGroupPointsTorsionFree.{u} := formal_group_points_no_prime_to_p_torsion
theorem torsionIntegral : TorsionIntegral.{u} := torsionIntegral_of formal_group_points_no_torsion

theorem isoExpand : IsoExpand.{u} := isogeny_expansion
theorem isoVanish : IsoVanish.{u} := isogeny_vanishing

theorem changeIntegral : ChangeIntegral.{u} := change_of_variables_integral

theorem lwP₂ : LogWeight.{u} := logarithm_coeff_weight
theorem unitCancel : UnitCancel.{u} := unit_cancellation

theorem compExpWeight : CompExpWeight.{u} := comp_exp_coeff_weight

theorem lemma2Weights : EllipticTorsionWeights.{u} := coefficient_weights_lemma_two
theorem frobExpand : FrobExpand.{u} := frobenius_expansion

theorem wSeriesUnique : WSeriesUnique.{u} := wSeriesExistsUnique_holds
theorem wSeriesLead : WSeriesLead.{u} := wSeriesLeadingTerm_holds
theorem wSubstUnique : WSubstUnique.{u} := wSeriesSubstUnique_holds
theorem wPoint : WPoint.{u} := wSeriesNonsingularPoint_holds
theorem wChordSeries : WChordSeries.{u} := wChordSeries_of wSubstUnique
theorem wChordSubst : WChordSubst.{u} := wChordSubst_of wSeriesSubstUnique_holds
theorem wFormalGroup : WFormalGroup.{u} := by
  apply wFormalGroup_of <;> first | exact wChordSeries | exact wChordSubst | exact wPoint | exact wSubstUnique | exact wSeriesUnique | exact wSeriesLead

theorem formal_group_points_param : FormalGroupPointsParametrisation.{u} := by
  apply formal_group_points_param_of <;> first | exact intValuedZp | exact nAddSubgroup | exact nZpSmul | exact nPderiv | exact lwP₂ | exact unitCancel | exact compExpWeight | exact lemma2Weights | exact frobExpand | exact wFormalGroup | exact formal_group_points_subgroup | exact formal_group_points_no_torsion | exact isoExpand | exact isoVanish | exact changeIntegral | exact wPoint | exact wSubstUnique | exact wChordSubst | exact wChordSeries | exact veluIntegralModel | exact veluUSeries | exact modelUnit
theorem formal_group_points_hom : FormalGroupPointsHomomorphism.{u} := by
  apply formal_group_points_hom_of <;> first | exact wSubstUnique | exact wChordSubst | exact formal_group_points_param | exact wFormalGroup | exact wChordSeries | exact wPoint

theorem veluIntegralModel : VeluIntegralModel.{u} := velu_integral_model
theorem veluUSeries : VeluUSeries.{u} := velu_u_series

theorem cubeTwo : CubeTwo.{u} := cube_two
theorem cubeThree : CubeThree.{u} := chordDeterminantFactor_holds

end Formalism.ELL
end
end
