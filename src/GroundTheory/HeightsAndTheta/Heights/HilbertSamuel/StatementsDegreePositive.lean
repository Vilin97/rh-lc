module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def DegreePositive.Statement : Prop :=
  ∀ (F : Type) [Field F] (ι₀ : Type) [Fintype ι₀] (q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ι₀))) (D : ℕ),
    IsMultiProjPrime q →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun _ : Unit => ι₀) ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
