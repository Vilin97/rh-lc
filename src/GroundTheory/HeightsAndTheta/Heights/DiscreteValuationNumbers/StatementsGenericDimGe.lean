import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def GenericDimGe.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)),
    P.IsPrime → P.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) ≤ ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
