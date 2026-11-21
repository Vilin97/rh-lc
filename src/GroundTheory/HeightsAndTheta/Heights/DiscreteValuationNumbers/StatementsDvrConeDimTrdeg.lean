module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def DvrConeDimTrdeg.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)),
    IsMultiProjPrime P → P.comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) = ⊥ →
      ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) =
        (((Algebra.trdeg O (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P)).toENat + 1 : ℕ∞) : WithBot ℕ∞)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
