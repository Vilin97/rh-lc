module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernWeilNumbersOfDegreeEqChernIntegralStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqIntegralTopChernFormComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmoothStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodChernWeilOfGoodTopChernForm

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqIntegralTopChernFormComplexStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.degree_eq_integral_topChernForm_complex : GlobalTheory.Published.ChernDegreeComplex := by
  first | exact @GlobalTheory.ChernDegree.chernDegreeComplex | exact GlobalTheory.ChernDegree.chernDegreeComplex | (intros; apply GlobalTheory.ChernDegree.chernDegreeComplex <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetric

section

@[expose] public section

namespace GlobalTheory.ChernDegree

theorem chernWeilNumbers_holds : GlobalTheory.Published.ChernWeilNumbers :=
  GlobalTheory.T.chernWeilNumbers_of_degree_eq_chernIntegral GlobalTheory.T.degree_eq_integral_topChernForm_complex

end GlobalTheory.ChernDegree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetricStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric : GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernDegree.chernWeilNumbers_holds | exact GlobalTheory.ChernDegree.chernWeilNumbers_holds | (intros; apply GlobalTheory.ChernDegree.chernWeilNumbers_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodChernWeil

section

@[expose] public section

namespace GlobalTheory.GoodMetric

theorem goodChernWeil : GlobalTheory.Published.GoodChernWeil :=
  goodChernWeil_of_goodTopChernForm GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric GlobalTheory.T.fullFlagBundle_pushForward_formula

end GlobalTheory.GoodMetric
end
end
