module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointObjectExistsOfLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomExtDvrOfCardTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarieties
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CmPointClosed
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriodStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExactKeyFormulaProof
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcClauseClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointObjectExistsOfLawsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.cmPointObject_exists_of_laws : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → CMExistsSt := by
  first | exact @GlobalTheory.CM.ExObj.cmExists | exact GlobalTheory.CM.ExObj.cmExists | (intros; apply GlobalTheory.CM.ExObj.cmExists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmExistsClosed

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem cmExists_closed : CMExistsSt :=
  GlobalTheory.T.cmPointObject_exists_of_laws GlobalTheory.T.exists_cmEllipticCurve_withPeriod GlobalTheory.cmPoint_closed GlobalTheory.thetaUnifAV_closed
    GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    (GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional)
    GlobalTheory.kernelFiniteFlat_holds

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem known_holds : Known :=
  have hL := GlobalTheory.firstFiveLaws
  have hh : GlobalTheory.CM.HomExtDvr := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr
  { laws := hL.1
    laws2 := hL.2.1
    ubc := hL.2.2.2.1.unifBaseChange
    laws5 := hL.2.2.2.2
    theta := GlobalTheory.thetaUnifAV_all
    n1ab := GlobalTheory.Moduli.jointExistence_and_moduliScheme.2
    n1c := GlobalTheory.closing_of_abelianSchemeLaws
    n5 := GlobalTheory.arcClause_closed
    models := GlobalTheory.Moduli.jointExistence_and_moduliScheme.1
    hom := hh
    key := GlobalTheory.KeyFam.keyFormula_holds
    cm := GlobalTheory.cmExists_closed
    deg := GlobalTheory.CM.PureDeg.degSt GlobalTheory.cmCurve_closed GlobalTheory.thetaUnifAV_all hL.1 hh
    ev := fun E _ _ _ H Dw l Xo c => (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1 }

end GlobalTheory.ArcCM
end
end
