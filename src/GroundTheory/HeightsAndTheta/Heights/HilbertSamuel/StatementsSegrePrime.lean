import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegrePrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime q →
    IsMultiProjPrime (segrePrime F q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
