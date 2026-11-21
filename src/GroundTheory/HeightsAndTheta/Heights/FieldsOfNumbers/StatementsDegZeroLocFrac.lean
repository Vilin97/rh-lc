module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocFrac.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W) →
    haveI := hP.isPrime
    ∀ x ∈ homFracDegZero P, ∃ y ∈ degZeroLoc P 𝒲, ∃ z ∈ degZeroLoc P 𝒲, z ≠ 0 ∧ x = y / z

end

end GroundTheory.Heights₂.Heights.FieldNumbers
