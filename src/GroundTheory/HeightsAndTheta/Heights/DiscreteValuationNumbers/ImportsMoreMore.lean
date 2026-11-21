module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisFurther
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def VerticalDivisorFibreVariety.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g →
    ∀ W ∈ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g).support,
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d

end GroundTheory.Heights₂.Heights.NumbersDVR
