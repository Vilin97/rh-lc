module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Mathlib.Analysis.Normed.Algebra.GelfandRadius

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMeasurableIsFundamentalDomain

section

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.LatticeFD

theorem exists_measurable_isFundamentalDomain (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ)
    [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] :
    ∃ 𝓕 : Set (GA E N), MeasurableSet 𝓕 ∧ ∀ μ : Measure (GA E N), IsFundamentalDomain (latticeGL E N) 𝓕 μ :=
  ⟨GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E N), GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom _,
    fun μ => GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ μ⟩

end GlobalTheory.CompanionTheory.LatticeFD

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGL

section

@[expose] public section

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

theorem exists_isFundamentalDomain_of_isSqInt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
      (μ : Measure (GA E N)) [μ.IsHaarMeasure] (φ : GA E N → ℂ), IsSqInt φ →
      ∃ F : Set (GA E N), IsFundamentalDomain (latticeGL E N) F μ := by
  intro E _ _ _ N _ _ μ _ φ _
  obtain ⟨F, -, hF⟩ := GlobalTheory.CompanionTheory.LatticeFD.exists_measurable_isFundamentalDomain E N
  exact ⟨F, hF μ⟩

end GlobalTheory.CompanionTheory.FinDisc

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFundamentalDomainGLStatement

section

@[expose] public section

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

theorem _root_.GlobalTheory.T.exists_fundamental_domain_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (φ : GA E N → ℂ), IsSqInt φ →
  ∃ F : Set (GA E N), IsFundamentalDomain (latticeGL E N) F μ := by
  first | exact @GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt | exact GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt | (intros; apply GlobalTheory.CompanionTheory.FinDisc.exists_isFundamentalDomain_of_isSqInt <;> assumption)
end
end
