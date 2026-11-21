module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegreDimGe.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (e : ℕ), IsMultiProjPrime q →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ((e + 1 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ∀ k, ι k) ⧸ segrePrime F q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
