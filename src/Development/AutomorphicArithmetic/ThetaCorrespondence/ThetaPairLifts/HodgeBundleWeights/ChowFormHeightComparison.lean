module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.VuSelfKnownTheorem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeilHeightInequality
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHolds
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowDegreeSection
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DescEval
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FormHeightOneEq
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IsClosedOfCoheight
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ResGAppLE
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SpecializesIff
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SumNormSqUnitary
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.OfLeaves
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IntegralOfLintegral
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.StCharts
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices

-- Source module: GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero

section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Matrix

section Objects

variable {n : ℕ}



def specFirst {R : Type*} [CommRing R] {e : ℕ} (u : Fin n → R) :
    MvPolynomial (Fin (e + 1) × Fin n) R →ₐ[R] MvPolynomial (Fin e × Fin n) R :=
  aeval fun p => Fin.cases (motive := fun _ => MvPolynomial (Fin e × Fin n) R) (C (u p.2))
    (fun k => X (k, p.2)) p.1


end Objects


end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHoldsStatement

section

@[expose] public section

open MvPolynomial NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Short ReciprocityTheory.ChartRestriction.G.T0

theorem _root_.GlobalTheory.T.mahler_section_statement_holds : GroundTheory.Heights₂.Heights.MahlerSection.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.mahlerSection | exact GlobalTheory.CompanionTheory.Ar.Short.mahlerSection | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.mahlerSection <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowFormHeightOfArch

section

@[expose] public section

namespace ChowFormHeightComparison₂.CF

open GroundTheory.Heights₂.Heights in
theorem chowFormHeight_of_arch (hA : StArch) (hM : MahlerSection.Statement) (hE : GlobalTheory.Published.ArExists) :
    PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  glue (stMain_of (stVert stPts stPull stDiv) hA
    (ChowHeightRecursion.of_leaves ChowFormSectionVertical.full hM ChowFormBaseChange.full BaseChangeAvoid.full)
    ChowFormSection.full ChowHeightMul.full ProjPrimeHasPoint.full) stModel stForm hE

end ChowFormHeightComparison₂.CF
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ChowFormHeightComparison

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
theorem ChowFormHeightComparison₂.chow_form_height_bound (h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  ChowFormHeightComparison₂.CF.chowFormHeight_of_arch (ChowFormHeightComparison₂.CF.stArch ChowFormHeightComparison₂.CF.stPts (ChowFormHeightComparison₂.CF.stCharts ChowFormHeightComparison₂.CF.stPts)) GlobalTheory.T.mahler_section_statement_holds h.p4.arExists
theorem ChowFormHeightComparison₂.chow_form_height_comparison : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) :=
  fun h => _root_.PositivityTheory.UnitarySelfGeneration.weil_height_inequality (_root_.ChowFormHeightComparison₂.chow_form_height_bound h) h
end
end
end
