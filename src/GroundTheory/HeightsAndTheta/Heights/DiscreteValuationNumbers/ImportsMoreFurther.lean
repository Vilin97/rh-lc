module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

def VerticalDivisorCharacterisation.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (ϖ : O)
    (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), Irreducible ϖ → IsMultiProjPrime P →
    (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g ↔ IsVerticalDivisor P ϖ b f g)

end GroundTheory.Heights₂.Heights.NumbersDVR
