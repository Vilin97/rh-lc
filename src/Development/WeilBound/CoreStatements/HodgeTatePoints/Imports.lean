module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.InterNumRestrictSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RestrLenRestrictSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsTildeVanish
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltBis
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech
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
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealXgen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauINontrivial
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish

-- Source module: GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGradedCech

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem GradedCech.proof : GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof

end GroundTheory.Heights₂.Heights.Swarm
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVanishingCechResidue

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem serreVanishing_graded_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}

end

end GroundTheory.Heights₂.Heights.KeyFormula
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.Imports

section

@[expose] public section

namespace PositivityTheory.HtPt.Ktw

theorem a1 :
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.Statement.{0, 0} :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Swarm.GradedCech.proof).mpr
    GroundTheory.Heights₂.Heights.KeyFormula.serreVanishing_graded_holds

theorem a2 :
    GroundTheory.Heights₂.Heights.Kleiman.TildeVanish.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.TildeVanish.proof a1

theorem a3 :
    GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed.proof
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof
    GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily.proof a2

theorem a4 :
    GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict.proof a3
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof

theorem a5 :
    GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict.proof a4

end PositivityTheory.HtPt.Ktw
end
end
