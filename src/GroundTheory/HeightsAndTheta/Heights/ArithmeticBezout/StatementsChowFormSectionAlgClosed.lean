import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionPerfect
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def ChowFormSectionAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle I u) W : ℤ))) e (specFirst f u)

end GroundTheory.Heights₂.Heights
