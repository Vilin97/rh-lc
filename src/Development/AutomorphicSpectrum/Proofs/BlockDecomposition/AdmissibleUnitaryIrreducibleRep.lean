import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExpStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageRight
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SesqEqZeroOfDiagEqZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.RealPlaceAnalysis.Complexify
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariant
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsGlobalCharDetPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.admitted

theorem isAdmissible_of_unitary_irreducible : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    PositivityTheory.Tls2.Iua.AdmG G → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn G σ → Formalism.MainNotions.S.IsIrredOn G σ →
    GlobalTheory.LinRed.IsAdmOn G σ := by
  intro n G hG hA H _ _ _ σ hσ hirr
  refine ⟨hσ.1, hσ.2.2, fun k hk v => hσ.2.1 k hk.1 v, ?_⟩
  intro S hfd hS _
  haveI := hfd
  let b := Module.finBasis ℂ S
  choose Y hYfd _ hvY hY using fun i => hA H σ hσ hirr S hS (b i) (b i).2
  haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYfd
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ, rfl, hΘ⟩
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap (Θ.domRestrict S)).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ GlobalTheory.LinRed.maxCpt G, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    have hks : k.conjTranspose ∈ GlobalTheory.LinRed.maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
    have hiso : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (σ k : H →ₗ[ℂ] H) (hσ.2.1 k hk.1)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (σ k u) : S) : H) = σ k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : σ k (σ k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hk.1 _ hks.1, hk1, hσ.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    have h := hΘ k hk _ (S.orthogonalProjectionOnto u).2
    simpa [T, hP] using h
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v = ((⟨v, hv⟩ : S) : H) := rfl
  rw [hv', ← b.sum_repr ⟨v, hv⟩]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T] using this

end GlobalTheory.CompanionTheory.admitted

end
