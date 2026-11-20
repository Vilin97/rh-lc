import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def MultAtOfSaturated.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) (ι : K → Type) (J Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [Q.IsPrime],
    J ≤ Q → (∀ q ∈ Q, ∃ s ∉ Q, s * q ∈ J) → Q ∈ J.minimalPrimes ∧ multAt J Q = 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
