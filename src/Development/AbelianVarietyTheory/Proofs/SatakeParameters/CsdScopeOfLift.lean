import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairBaseChangePolarizedSameWeight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestriction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvableStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.CsdLift

theorem val_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).val w = 1 := by
  rfl

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

theorem compNorm_quadChar_pow (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) :
    compNorm E (quadChar E ^ a) = 1 := by
  rw [map_pow, compNorm_quadChar, one_pow]

end GlobalTheory.CsdLift

end
