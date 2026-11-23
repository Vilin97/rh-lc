module

public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Formalism.HermitianCurvature.HerGenC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiExistsOfIn
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundDiscreteSeriesCoefficients

-- Source module: Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ActualClassesCompactSupport

section

@[expose] public section

namespace GlobalTheory

theorem actualClasses_compactSupport : Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  Formalism.FourierDecayAlt.P.CutSE.actual_compact_theorem

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselXiIntegrableHolds

section

@[expose] public section

namespace GlobalTheory

theorem besselXiIntegrable_holds : GlobalTheory.HCXi.BesselXiIntegrable :=
  ReciprocityTheory.ChartRestriction.DS.Xi.xiExists

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundDiscreteSeriesCoefficientsStatement

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt

theorem _root_.GlobalTheory.T.pointwiseBound_discreteSeries_coefficients : GlobalTheory.HCXi.BesselXiIntegrable → P5.ThmPActualCpt → ThmBpDS := by
  first | exact @GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries | exact GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries | (intros; apply GlobalTheory.BpDiscreteSeriesTwoInputs.pointwise_bound_discreteSeries <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional

section

@[expose] public section

open BpJoin

namespace GlobalTheory

theorem discreteSeriesCoef_pointwiseBound : ThmBpDS :=
  GlobalTheory.T.pointwiseBound_discreteSeries_coefficients GlobalTheory.besselXiIntegrable_holds GlobalTheory.actualClasses_compactSupport

end GlobalTheory
end
end
