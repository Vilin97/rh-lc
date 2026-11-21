import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfSecCoord

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.Ex.OneGen GlobalTheory.ThetaPtMove
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.Model

theorem polFib_self {R : Type} [CommRing R] (P : PolAV (Sp R)) : PolFib P.A P.L P.g (𝟙 _) := by
  exact ⟨P, 𝟙 _, rfl, @isGrpPullback_of_iso _ _ _ _ _ (Iso.refl P.A) (inferInstanceAs (IsMonHom (𝟙 P.A))),
    (GlobalTheory.PolBaseChange.lbIso_refl P.isLB).chartPull (chartPullId _) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl)⟩

end GlobalTheory.UMin.Model
