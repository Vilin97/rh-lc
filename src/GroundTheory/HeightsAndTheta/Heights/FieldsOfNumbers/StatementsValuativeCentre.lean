import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ValuativeCentre.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hP : IsMultiProjPrime P),
    haveI := hP.isPrime
    ∀ R : ValuationSubring (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)),
      (∀ c : F, algebraMap F (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) c ∈ R) →
      ∃ y : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiProjPrime y ∧ P ≤ y ∧
        ∀ (b : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) (Ideal.Quotient.mk P f) /
              algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P g) ∈ R ∧
            (f ∈ y ↔ algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P))
                (Ideal.Quotient.mk P f) / algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P g) ∈
              R.nonunits)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
