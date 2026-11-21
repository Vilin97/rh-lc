module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocResidue.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι))
    [P.IsPrime] (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) [W.IsPrime], P ≤ W →
    ∃ ρ : degZeroLoc P {W} →+* FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ W),
      (∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog f b →
        IsMultiHomog g b → g ∉ W →
        (x : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) =
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P f) /
            algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P g) →
        ρ x = algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ W) _ (Ideal.Quotient.mk W f) /
            algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ W) _ (Ideal.Quotient.mk W g)) ∧
      (∀ x : degZeroLoc P {W},
        ρ x = 0 ↔ ¬ ∃ y ∈ degZeroLoc P {W}, (x : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) * y = 1) ∧
      ∀ z : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ W), z ∈ homFracDegZero W ↔ ∃ x, ρ x = z

end

end GroundTheory.Heights₂.Heights.FieldNumbers
