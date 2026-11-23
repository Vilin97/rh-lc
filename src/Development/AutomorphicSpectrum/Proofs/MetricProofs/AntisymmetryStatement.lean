module

public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdjacentSwapHeightPolynomialRelationStatement
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Mathlib.Algebra.MvPolynomial.Funext
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightPolynomialWeightForm
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagVarietyAnalyticSystemExistsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FormPolyIsHomogeneousAndEval
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GapEqWeightSubNextStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProportionalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibilityStatement
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.WeightMapInjective
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.EtaleLocalizationAtPrimeTensorOfEtaleAway

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open MvPolynomial GroundTheory.Heights₂.Heights

theorem mem_antisymSpace_of_pointwise :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : MvPolynomial (Ψ × Fin N) ℝ),
      R.IsHomogeneous (antisymDegree Ψ N + 1) →
      (∀ (τ : Ψ) (a b : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) →
        ∀ lam : Ψ × Fin N → ℝ, eval lam R + eval (lam ∘ Equiv.swap (τ, a) (τ, b)) R = 0) →
      R ∈ antisymSpace Ψ N j := by
  intro Ψ _ _ N j R hR h
  refine ⟨(mem_homogeneousSubmodule _ _).2 hR, ?_⟩
  rintro σ ⟨τ, a, b, hab, hblock, rfl⟩
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_rename, map_neg]
  exact eq_neg_of_add_eq_zero_right (h τ a b hab hblock lam)

end GlobalTheory.CompanionTheory.Ar.PB
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PluriharmonicCharts.XTsgSmul

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.tsg_smul

theorem toWt_inj (Ψ : Type) (N : ℕ) :
    Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  apply GlobalTheory.CompanionTheory.Ar.Top.FlDeg.toWt_leftInverse_injective <;> assumption

end PositivityTheory.Xgp.tsg_smul

theorem PositivityTheory.Xgp.t_tsg_smul : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  refine ⟨?_, ?_, fun Ψ N => PositivityTheory.Xgp.tsg_smul.toWt_inj Ψ N⟩
  · intro D κ v Q
    by_cases hv : v = 0
    · subst hv
      simp [tsgPoly]
    · simp only [tsgPoly, Polynomial.natDegree_C_mul hv, Polynomial.coeff_C_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs
      · simp only [Polynomial.C_mul]
        ring
      · simp
  · intro σ c e v Q
    simp [linePoly, Polynomial.algebraMap_eq]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightTransformInjectiveLinear

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tsgPoly_linePoly_smul_toWt_injective :
    (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) :=
  PositivityTheory.Xgp.t_tsg_smul

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightTransformInjectiveLinearStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.weight_transform_injective_linear : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective | exact GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.tsgPoly_linePoly_smul_toWt_injective <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.Antisymmetry

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.Top

theorem antisymmetry : Antisymmetry := by
  intro hIn II hII Ψ _ _ _ N j d hN S K _ ι _ P Re hF
  obtain ⟨d₀, S₀, Re₀, hd₀, hdeg₀, href₀, hline₀, ⟨hF₀⟩⟩ := GlobalTheory.T.flag_variety_analytic_system_exists hIn Ψ N hN
  have hdim : d + 1 = antisymDegree Ψ N := hF.dim
  obtain rfl : d = d₀ := by omega
  have hS := ((GlobalTheory.T.proportional' hIn Ψ N j hN hF.j_le).2 (d + 1) S hdim hF.unif).2
  have hpot := GlobalTheory.T.realisation_potential_degree_compatibility hIn.2.1.1 (FlBlock Ψ N) (FlIdx Ψ N) (d + 1) (Ψ × Fin N) S₀ (PFl Ψ N) Re₀
  have harith : IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
    rw [← hdim]; exact Re₀.arith
  have hfl := flLines_polys hIn II hII Ψ N hN harith

  have hdeg0 : toWt S₀.degPoly = degFlPoly Ψ N := by
    have h2 := hfl.2
    rw [← hdim] at h2
    rw [h2]
    congr 1
    unfold AnSys.degPoly
    congr 1
    funext w
    have h3 := hpot.2.1 w
    simp only [href₀, hdeg₀, Nat.cast_one, one_mul] at h3
    exact h3.symm

  have hPB0 : toWt (Re₀.PB II) = hFlPoly Ψ N II := by
    have h1 := hfl.1
    rw [← hdim] at h1
    rw [h1]
    congr 1
    unfold Realis.PB
    congr 1
    funext w
    unfold Realis.limNum Realis.num
    simp only [hline₀, hdeg₀, Nat.cast_one, div_one]
    exact tendsto_const_nhds.limUnder_eq

  have hdegS : S.degPoly = C (volOf S) * S₀.degPoly := by
    apply (GlobalTheory.T.weight_transform_injective_linear).2.2 Ψ N
    rw [hS, map_mul, hdeg0]
    congr 1
    simp [toWt, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

  obtain ⟨Cst, hC⟩ := GlobalTheory.T.weighted_polynomial_homogeneous_coeff_bound Ψ N (antisymDegree Ψ N + 1)
  have hhomT : (toWt (Re.PB II)).IsHomogeneous (antisymDegree Ψ N + 1) := by
    refine (hC.1 _ 0 ?_).1
    rw [← hdim]
    exact (formPoly_isHomogeneous_and_eval (Ψ × Fin N) (d + 1 + 1) (Re.limNum II)).1
  have hhomH : (hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) :=
    (formPoly_isHomogeneous_and_eval (Ψ × Fin N) _ _).1
  have hhom : (toWt (Re.PB II) - volOf S • hFlPoly Ψ N II).IsHomogeneous (antisymDegree Ψ N + 1) := by
    have hm := (homogeneousSubmodule (Ψ × Fin N) ℝ (antisymDegree Ψ N + 1)).sub_mem
      ((mem_homogeneousSubmodule _ _).2 hhomT)
      (Submodule.smul_mem _ (volOf S) ((mem_homogeneousSubmodule _ _).2 hhomH))
    exact (mem_homogeneousSubmodule _ _).1 hm
  refine mem_antisymSpace_of_pointwise Ψ N j _ hhom ?_
  intro τ a b hab hj lam
  have e1 := GlobalTheory.T.adjacent_swap_height_polynomial_relation hIn II hII Ψ N d S K ι P Re τ a b hab (hF.sq τ a b hab hj) lam
  have e0 := GlobalTheory.T.adjacent_swap_height_polynomial_relation hIn II hII Ψ N d S₀ (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) Re₀ τ a b hab
    (hF₀.sq τ a b hab (Or.inl b.isLt)) lam
  rw [hPB0] at e0
  rw [hdegS, (GlobalTheory.T.weight_transform_injective_linear).2.1, (GlobalTheory.T.weight_transform_injective_linear).1, Polynomial.eval_mul, Polynomial.eval_C, ← e0] at e1
  simp only [map_sub, smul_eval]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.Top
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.AntisymmetryStatement

section

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.antisymmetry' : Antisymmetry := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Top.antisymmetry | exact GlobalTheory.CompanionTheory.Ar.PB.Top.antisymmetry | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Top.antisymmetry <;> assumption)
end
end
