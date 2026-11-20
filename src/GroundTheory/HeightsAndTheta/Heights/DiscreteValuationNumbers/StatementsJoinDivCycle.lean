import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx)

def JoinDivCycle.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι),
    ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) f) =
      Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f)

end GroundTheory.Heights₂.Heights.NumbersDVR
