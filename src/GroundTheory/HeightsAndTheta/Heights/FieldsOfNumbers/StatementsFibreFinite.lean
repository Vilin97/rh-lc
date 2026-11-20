import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FibreFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → (fibrePrimes j P' W).Finite

end

end GroundTheory.Heights₂.Heights.FieldNumbers
