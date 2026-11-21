module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegreePositive
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def MultiDegreePositive.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (e : ℕ), IsMultiProjPrime q →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
