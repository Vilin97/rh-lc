module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExistStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLawsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LevelRestrictionOfGroupLawHolds
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatibleStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaFunctionsOverTwoUnitAndIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugateStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaValuesVanishAtOddSplitPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugatesStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExistsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertPrimeOrderParitySignRadicalIntegralForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHoldsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPointsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlacesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditiveStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.theta_cube_relation_integral_formalGroup_biadditive : ∀ D : D7, GL3Theta.cube D ∧ GL3Theta.addInt D ∧ GL3Theta.beBiadd D := by
  first | exact @GlobalTheory.ThetaCube.cube_addInt_beBiadd | exact GlobalTheory.ThetaCube.cube_addInt_beBiadd | (intros; apply GlobalTheory.ThetaCube.cube_addInt_beBiadd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmNormalizedThetaJetsIntegral

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaJets

theorem jetsPh_all : ∀ D : D7, GL3Theta.jetsPh D := fun D =>
  Formalism.MainNotions.Ext.CutA.jetsPh_of' Formalism.MainNotions.Ext.CutA.jetsHigh_holds Formalism.MainNotions.Ext.CutA.jetsOne_holds
    Formalism.MainNotions.Ext.CutA.jetsTwo_holds D (GlobalTheory.T.theta_cube_relation_integral_formalGroup_biadditive D).1 (GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D).2.1 (GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D).2.2

end GlobalTheory.ThetaJets
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmNormalizedThetaJetsIntegralStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.cm_normalized_theta_jets_integral : ∀ D : D7, GL3Theta.jetsPh D := by
  first | exact @GlobalTheory.ThetaJets.jetsPh_all | exact GlobalTheory.ThetaJets.jetsPh_all | (intros; apply GlobalTheory.ThetaJets.jetsPh_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaFunctionsOverTwoUnitAndIntegralStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.cm_theta_functions_over_two_unit_and_integral : ∀ D : D7, GL3Theta.atTwo D := by
  first | exact @GlobalTheory.EvenTheta.atTwo | exact GlobalTheory.EvenTheta.atTwo | (intros; apply GlobalTheory.EvenTheta.atTwo <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModelStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.datum_curve_integral_unitDisc_model : ∀ D : D7, GL3Theta.modelEx D := by
  first | exact @GlobalTheory.UnitModel.modelEx_holds | exact GlobalTheory.UnitModel.modelEx_holds | (intros; apply GlobalTheory.UnitModel.modelEx_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCmStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm : ∀ D : D7, oddRep D := by
  first | exact @GlobalTheory.NormSum.exists_rep_trivial_at | exact GlobalTheory.NormSum.exists_rep_trivial_at | (intros; apply GlobalTheory.NormSum.exists_rep_trivial_at <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfied

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem inp_all : ∀ D, Inp D := fun D =>
  { g1 := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
    perm := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).2
    uni := GlobalTheory.T.intertwinerUnitary_all D
    mu := GlobalTheory.T.admissible_characters_exist D
    curve := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D
    gal := GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D
    galEx := GlobalTheory.T.galois_data_exists D
    t0Ex := GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D
    use1 := GlobalTheory.T.forall_use1 D
    alg := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D
    conj := GlobalTheory.T.thetaVacua_conjugates_cmPoints D
    nrm := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D
    bar := GlobalTheory.T.cmTheta_complexConjugation_compatible D
    odd3 := GlobalTheory.T.weilRepresentation_vacuum_sign_inert_places D
    odd4 := GlobalTheory.T.oddness_condition_holds D
    rep := GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm D
    model := GlobalTheory.T.datum_curve_integral_unitDisc_model D
    transl := GlobalTheory.T.cm_theta_torsion_translate_integral_series D
    two := GlobalTheory.T.cm_theta_functions_over_two_unit_and_integral D
    jets := GlobalTheory.T.cm_normalized_theta_jets_integral D
    split := GlobalTheory.T.cm_theta_values_vanish_at_odd_split_prime D
    eqv := GlobalTheory.OddRank.exact_equivariance D }

end GlobalTheory.NormSum
end
end
