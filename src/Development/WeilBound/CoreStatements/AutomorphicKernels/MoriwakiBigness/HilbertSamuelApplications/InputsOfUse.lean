module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInputStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCountStatement
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNef
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefF
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
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineFibreHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInput
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCount
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCount
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDoubleComplexVanish
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceRateStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystemStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RationalityOfResolutionStatementStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SignedConvergenceStatementHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHoldsStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.HsLinksOfUse

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanNefCriteriaHold

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem kleimanNef_field_and_fibre : KleimanNefIntersectionNonneg ∧ KleimanNefFStatement := by
  have hF : KleimanNefFStatement :=
    GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNefF.kleimanNef_field_of_alt (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).1
  exact ⟨GroundTheory.Heights₂.Heights.ForSecondHalf.KleimanNef.proof hF, hF⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanNefCriteriaHoldStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem _root_.GlobalTheory.T.kleiman_nef_criteria_hold : KleimanNefIntersectionNonneg ∧ KleimanNefFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre | exact GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre <;> assumption)
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.OfRemaining

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SiuZB.proof (hK : KodairaGeneric.Statement) (hZ : SectionsDimZero.Statement) : KH.SiuZStatement := by
  intro K _ ι _ Ω _ _ y D α I hI hV hB hNef hPos
  classical

  have hagree : ∀ (V : Ideal (MRingOver ℚ ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum ℚ V L := by
    obtain ⟨I₀, -, h₀⟩ := Targets.ExistsUnique.full ℚ ι
    intro V n L hVn
    rw [h₀ I hI V n L hVn, h₀ _ (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) V n L hVn]
  have hG : IsProjVarF (KH.genIdeal y) D := isProjVarF_map_of_isArithVar hV
  have hdeg : 0 < genDeg (mCoordIdeal y) D α := by
    have h := hagree _ D (fun _ => α) hG
    rw [h] at hPos
    exact hPos

  obtain ⟨k, e, hk, he, hmem⟩ :
      ∃ (k : ℕ) (e : Ω), 1 ≤ k ∧ e ≠ 0 ∧ e ∈ chartLatQ y ((k : ℤ) • α - 1) 1 := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have hr := hZ K ι Ω y ((1 : ℕ) • α - 1) 1 hV
      have hg : genDeg (mCoordIdeal y) 0 ((1 : ℕ) • α - 1) = genDeg (mCoordIdeal y) 0 α := by
        unfold genDeg
        congr 1
        funext j
        exact j.elim0
      rw [hg] at hr
      have hpos : 0 < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1) := by
        have : (0 : ℤ) < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1) := by rw [hr]; exact hdeg
        exact_mod_cast this
      have := Module.nontrivial_of_finrank_pos hpos
      obtain ⟨⟨e, he⟩, hne⟩ := exists_ne (0 : chartLatQ y ((1 : ℕ) • α - 1) 1)
      refine ⟨1, e, le_rfl, fun h => hne ?_, by simpa using he⟩
      exact Subtype.ext h
    · have hnef : NefOnGenericDeg (mCoordIdeal y) α := by
        intro W hW hPW
        have hWq : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
          isProjVarF_map_of_isArithVar (D := 1) hW
        have h := hNef _ hWq (Ideal.map_mono hPW)
        rw [hagree _ 1 _ hWq] at h
        unfold genDeg
        convert h using 2
        funext j
        fin_cases j
        rfl
      exact hK K ι Ω y D α hD hV hB hnef hdeg

  obtain ⟨n, hn, hns⟩ := ChartDenominator.proof K ι Ω y ((k : ℤ) • α - 1) 1 e hmem
  have hn0 : (n : Ω) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨k, hk, (n : Ω) * e, ?_, mul_ne_zero hn0 he⟩
  have hfun : (fun κ => (k : ℤ) * α κ - 1) = (k : ℤ) • α - 1 := by
    funext κ
    simp
  rw [hfun]
  exact hns

theorem SiuZB.of_kodaira (hK : KodairaGeneric.Statement) : KH.SiuZStatement :=
  SiuZB.proof hK SectionsDimZero.proof

end GroundTheory.Heights₂.Heights.ForSecondHalf
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SiuInequalityIntegralHolds

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem siuZ : SiuZStatement := by
  have hR4 := GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput
  obtain ⟨-, hVA, hSC⟩ := GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count hR4
  exact GroundTheory.Heights₂.Heights.ForSecondHalf.SiuZB.of_kodaira (GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count hVA hSC)

end GlobalTheory.CompanionTheory.Ar.Giv
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SiuInequalityIntegralHoldsStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

theorem _root_.GlobalTheory.T.siu_inequality_integral_holds : SiuZStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.siuZ | exact GlobalTheory.CompanionTheory.Ar.Giv.siuZ | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.siuZ <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.InputsOfUse

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem inputs_of_use :
    ArithIntersectionSystemStatement → PositivityTheory.MbHsUse.HSUse →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ResK.ResKStatement → GlobalTheory.CompanionTheory.Ar.PB.Inputs := by
  intro hII hU hBig hRes
  exact ⟨⟨GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds, GlobalTheory.T.pullback_statement_holds, GlobalTheory.T.global_regularization_statement_holds⟩,
    ⟨GlobalTheory.T.resolution_exists_of_resolution_statement hRes, degree_of_system hII, (hsLinks_of_use hU hBig).1⟩,
    ⟨GlobalTheory.T.rationality_of_resolution_statement hRes, metricLocal⟩,
    ⟨GlobalTheory.T.projection_formula_of_arith_system hII, lineFibre_holds, fibreDim⟩,
    ⟨GlobalTheory.T.kleiman_nef_criteria_hold.1, GlobalTheory.T.kleiman_nef_criteria_hold.2, GlobalTheory.T.siu_inequality_integral_holds⟩⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end
end
