import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConePolyLocalization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarUnit.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hP : IsMultiProjPrime P)
    (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ (p : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ), IsUnit (p.coeff e) →
      IsUnit (coneVarMap P W hPW v p)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
