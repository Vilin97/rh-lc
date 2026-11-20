import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConePolyLocalization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarNumerator.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hP : IsMultiProjPrime P)
    (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ p : MvPolynomial K (degZeroLoc P {W}),
      ∃ (b : K → ℕ) (g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) (h : (K →₀ ℕ) → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι),
        IsMultiHomog g b ∧ g ∉ W ∧ (∀ d, IsMultiHomog (h d) b) ∧
        (∀ d, ((p.coeff d : degZeroLoc P {W}) : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) =
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) (Ideal.Quotient.mk P (h d)) /
            algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P g)) ∧
        ((coneVarMap P W hPW v p : coneLocal P W hPW) : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)) =
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P))
              (Ideal.Quotient.mk P (∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ^ d k)) /
            algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) _ (Ideal.Quotient.mk P g)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
