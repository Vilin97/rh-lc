module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocQuot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι))
    [P.IsPrime] (𝒲 : Set (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι))), (∀ W ∈ 𝒲, W.IsPrime) →
    ∀ x ∈ degZeroLoc P 𝒲, ∃ (b : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog f b ∧ IsMultiHomog g b ∧
      g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧
      x = algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P g)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
