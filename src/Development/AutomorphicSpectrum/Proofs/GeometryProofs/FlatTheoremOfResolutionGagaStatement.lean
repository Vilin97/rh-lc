module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantAllHoldsStatement
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
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfParts
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHolds

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem finConst_of_all_hosts : FinConst :=
  FinConstAll.finConst GlobalTheory.T.finite_constant_all_holds

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHoldsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.finite_constant_holds : GlobalTheory.CompanionTheory.Ar.Flat.FinConst := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | exact GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.finConst_of_all_hosts <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfPartsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.flat_theorem_of_parts : PartI → FlatLineGenerator → FlatLineGeneratorComponent → FinConst → ThmFlatA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_parts | exact GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_parts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_parts <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem thmFlatA_of_resK_gaga_partI :
    Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA :=
  fun hR hG hP =>
    GlobalTheory.T.flat_theorem_of_parts hP (GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG) (GlobalTheory.T.flat_first_from_resolution_and_gaga hR hG) GlobalTheory.T.finite_constant_holds

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGagaStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.flat_theorem_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI | exact GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI <;> assumption)
end
end
