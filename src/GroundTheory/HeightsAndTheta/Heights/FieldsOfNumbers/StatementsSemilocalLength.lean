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

set_option synthInstance.maxHeartbeats 400000 in

def SemilocalLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a h : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))), IsMultiHomog a c → IsMultiHomog h c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → h ∉ W →
    ∀ M : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι') → ℤ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        M W' = relDeg j W') →
      (∀ W', contractPrime j W' ≠ W → M W' = 0) →
      haveI := hP'.isPrime
      ∀ α : degZeroLoc (contractPrime j P') {W},
        (α : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k)) ⧸ contractPrime j P')) =
            algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k)) ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') a) /
              algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k)) ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') h) →
          ∃ N : ℕ, Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸
                LinearMap.range (LinearMap.lsmul (degZeroLoc (contractPrime j P') {W})
                  (degZeroLoc P' (fibrePrimes j P' W)) α)) = N ∧
            cycEval M ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P' (rename (blockIncl j ι') a)) W : ℤ))) = N

end

end GroundTheory.Heights₂.Heights.FieldNumbers
