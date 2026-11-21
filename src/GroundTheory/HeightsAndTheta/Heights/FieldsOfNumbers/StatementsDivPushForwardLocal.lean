module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForward
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PPFContractedDim
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PRelevantPrimeDimGe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivPushForwardLocal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))), IsMultiHomog a c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))), IsMultiProjPrime W → relDim W = (n : ℕ) →
    ∀ M : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι') → ℤ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        M W' = relDeg j W') →
      (∀ W', contractPrime j W' ≠ W → M W' = 0) →
      haveI := hP'.isPrime
      cycEval M ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P' (rename (blockIncl j ι') a)) W : ℤ))) =
        relDeg j P' * ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (contractPrime j P') a) W : ℤ)

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
