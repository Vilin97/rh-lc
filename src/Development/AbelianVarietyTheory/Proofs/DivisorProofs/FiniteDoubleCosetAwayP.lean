import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesFiniteClassDecomposition
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowNormOneIdeleEqPrincipalMulIntegralUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugacyClassClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitsLocallyCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCentralizerTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryPointsAtPlaceFstMemCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOrbitCentralizerAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointOfEventuallyIntegralLocaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactUnitaryAdelicProdLocalCompactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyCompactUnitaryAdelicImageIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryPointsAtPlaceMulMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactIntegralUnitaryPointsAtPlaceStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigIterateApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFrStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CycFieldA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsB
import Development.AbelianVarietyTheory.Definitions.Divisors.ShiftTw
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedSimilitudePairMinpolyRootsNormSqEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousFiniteAdeleEquivRatIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRestrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFiniteAdelesSplitAwayFromPrimePadicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitIdempotentConjugation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCentralizerRegularTwistedCentraliserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtPStatement

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.CentTorus
open scoped TensorProduct

namespace GlobalTheory.CentTorus.AdelicSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

end Tmap

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

theorem adele_split (p : ℕ) [Fact p.Prime] :
    ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p) (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
  obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
  let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
  exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom, (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩

end GlobalTheory.CentTorus.AdelicSplit

section Final

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

end Final
