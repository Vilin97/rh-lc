module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeLocalLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hP : IsMultiProjPrime P)
    (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hW : IsMultiProjPrime W), P ≤ W →
    ∀ (c : K → ℕ) (a h : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog a c → IsMultiHomog h c → h ∉ W →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ α : degZeroLoc P {W},
      (α : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) =
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P a) /
            algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P h) →
        multAt (P ⊔ Ideal.span {a}) W =
          Ring.ord (degZeroLoc P {W}) α

end

end GroundTheory.Heights₂.Heights.FieldNumbers
