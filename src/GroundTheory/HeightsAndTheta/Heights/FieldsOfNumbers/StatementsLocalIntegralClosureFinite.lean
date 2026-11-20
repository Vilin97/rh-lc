import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def LocalIntegralClosureFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))), IsMultiProjPrime W → contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ s : Finset (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι' ⧸ P')),
        (∀ e ∈ s, e ∈ homFracDegZero P' ∧
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) e) ∧
        ∀ x ∈ homFracDegZero P',
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) x →
          x ∈ Submodule.span ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P'))
            (s : Set (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι' ⧸ P')))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
