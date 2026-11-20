import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def VerticalDivisorJoinPullback.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    IsVerticalDivisor (pointIdeal O y) ϖ b f g →
      IsVerticalDivisor (pointIdeal O (joinCoords y y')) ϖ (joinDeg b) (joinForm f) (joinForm g)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
