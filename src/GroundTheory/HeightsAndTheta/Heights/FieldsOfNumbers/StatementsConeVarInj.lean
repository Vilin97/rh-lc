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

def ConeVarInj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hP : IsMultiProjPrime P)
    (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    Function.Injective (coneVarMap P W hPW v)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
