module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConePolyLocalization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarSurj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hP : IsMultiProjPrime P)
    (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ z : coneLocal P W hPW, ∃ (p q : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ),
      IsUnit (q.coeff e) ∧ z * coneVarMap P W hPW v q = coneVarMap P W hPW v p

end

end GroundTheory.Heights₂.Heights.FieldNumbers
