module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivPushForward.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))), IsMultiHomog a c →
    a ∉ contractPrime j P' →
    ∀ (N' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι') → ℤ) (N : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))) → ℤ),
      (∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) →
        relDim (contractPrime j W') = (n : ℕ) →
        haveI := hW'.isPrime
        N' W' = relDeg j W' * N (contractPrime j W')) →
      (∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) → relDim (contractPrime j W') < (n : ℕ) →
        N' W' = 0) →
      haveI := hP'.isPrime
      cycEval N' ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P' (rename (blockIncl j ι') a)) W : ℤ))) =
        relDeg j P' * cycEval N ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (contractPrime j P') a) W : ℤ)))

open Classical in

end

end GroundTheory.Heights₂.Heights.FieldNumbers
