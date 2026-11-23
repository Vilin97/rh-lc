module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NonvanishingPointsDense

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.nonvanishing_points_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof)
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishing

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem nonvanishing_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact @PositivityTheory.Xgn.nonvanishing_points_dense

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishingStatement

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.complex_points_dense_nonvanishing : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | exact GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.nonvanishing_dense <;> assumption)
end
end
