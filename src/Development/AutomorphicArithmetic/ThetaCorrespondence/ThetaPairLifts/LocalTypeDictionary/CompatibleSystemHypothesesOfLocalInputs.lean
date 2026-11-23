module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OfClassification
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsFinDimLink
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
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
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MassRatioAllUnramifiedCmFields

section

@[expose] public section

open Formalism.MainNotions

namespace GlobalTheory.Mass

theorem massRatio_all_unramified_cmFields : StandardLattice.SiegelMassRatioCM :=
  Formalism.MainNotions.StandardLattice.standardMassRatio_of_modelMassRatio GlobalTheory.Mass.siegelMassRatio_holds

end GlobalTheory.Mass
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteSeriesThreeOfHyp

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem discreteSeries_three_of_hypotheses (hC : GlobalTheory.Published.DiscreteSeriesCoverExists) :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) ∧ (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) ∧ (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) := by
  intro hE hU
  refine ⟨fun n ε lam hl => ?_, fun n ε lam hl H H' _ _ _ _ σ σ' hσ hσ' => hU n ε lam hl H H' σ σ' hσ hσ', hC⟩
  obtain ⟨H, i1, i2, σ, h1, h2, h3, h4, h5, h6, h7⟩ := hE n ε lam hl
  exact ⟨H, i1, i2, σ, h1, h2, h3, h4, h5, h6, h7⟩

end GlobalTheory
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CompatibleSystemHypothesesOfLocalInputs

section

@[expose] public section

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory
theorem compatibleSystem_hypotheses_of_localInputs : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Mem.Top.Bl.HypAAlt :=
  fun ar cm we hm cd cw hf cl ce fd sw =>
    have c := GlobalTheory.DiscreteSeriesConsequences.of_classification cl
    have u : GlobalTheory.Published.DiscreteSeriesUpqUnique := GlobalTheory.Published.discreteSeriesUpqUnique_of_classification cl
    have d := GlobalTheory.discreteSeries_three_of_hypotheses ce c.2.2.2.2 u
    ⟨ar.rayClassFieldSt, ar.principalIdealSt, cm, hm, cd, cw, GlobalTheory.weilRepresentationUnitaryPair, c.2.2.1, hf, c.2.1, u,
      GlobalTheory.rowsFinDim_link, sw, c.2.2.2.2, fd, GlobalTheory.Mass.massRatio_all_unramified_cmFields,
      d.1, d.2.1, d.2.2, ar, we⟩
end GlobalTheory
end

section
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.LiteralAutomorphy

theorem _root_.GlobalTheory.T.compatibleSystem_member_hypotheses : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCoverExists → GlobalTheory.Published.FormalDegreeCompactDual → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Mem.Top.Bl.HypAAlt := by
  first | exact @_root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs | exact _root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs | (intros; apply _root_.GlobalTheory.compatibleSystem_hypotheses_of_localInputs <;> assumption)
end
end
end
