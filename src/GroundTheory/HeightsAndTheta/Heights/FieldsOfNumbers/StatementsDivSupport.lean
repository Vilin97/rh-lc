import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivCycleSupport.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (c : K → ℕ) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog f c → f ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) ≠ 0 → IsMultiProjPrime W ∧ relDim W = (n : ℕ)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
