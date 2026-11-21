module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u u' v v' w

section Objects

def HasRelDim {F : Type u} [Field F] {K : Type v} [Fintype K] {ι : K → Type w}
    (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (n : ℕ) : Prop :=
  ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)

open Classical in

open Classical in

end Objects

open Classical in

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
