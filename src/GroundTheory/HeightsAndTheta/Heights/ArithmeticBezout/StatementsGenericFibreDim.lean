import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LinFormOneZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver IsArithVar PBlk)

def GenericFibreDim.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P d →
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ genericIdeal P) = ((d : ℕ) : WithBot ℕ∞)

end ObjectsChow

end GroundTheory.Heights₂.Heights
