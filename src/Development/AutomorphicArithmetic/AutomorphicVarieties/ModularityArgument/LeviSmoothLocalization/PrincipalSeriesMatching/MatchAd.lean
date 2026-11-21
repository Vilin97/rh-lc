import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2
import GroundTheory.AutomorphicForms.MeasuresGL
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.EulerProducts.GenStable
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.GammaZeroLevelMembership
import GroundTheory.GlobalFields.CompletionAtPlace
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.GlobalFields.Artin.Series
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import GroundTheory.GlobalFields.NormResidueSymbol.RestrictNormalInfiniteLocalSymbol
import GroundTheory.GlobalFields.Artin.Places
import GroundTheory.GlobalFields.Artin.InflationTower
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.LocalFields.BrauerInductionClifford
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
import GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation
import GroundTheory.LocalFields.DifferentGalois
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeRatioPosOfPublished
import GroundTheory.GlobalFields.TateThesis.DedekindContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
import GroundTheory.GlobalFields.ClassFieldConsequences.TrivialModulus
import GroundTheory.GlobalFields.GlobalReciprocity.General
import GroundTheory.GlobalFields.ClassFieldConsequences.RayClassFieldLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductInductionSupported
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.GlobTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem unr_mul {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) : IsUnram (a * b) := fun x hx => by
  rw [MonoidHom.mul_apply, ha x hx, hb x hx, one_mul]

private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]

end Loc

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad in
