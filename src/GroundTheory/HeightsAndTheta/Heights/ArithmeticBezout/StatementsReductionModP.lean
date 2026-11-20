import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeGeoNum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver IsMultiProjPrime PBlk)

def ReductionModP.Statement : Prop :=
  ∀ (n p : ℕ) (W : Ideal (MRing (PBlk n))) (F : Type) [Field F],
    p.Prime → IsMultiProjPrime W → C (p : ℤ) ∈ W →
      Function.Surjective (Int.castRingHom F) → ((p : ℤ) : F) = 0 →
        IsProjPrime ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F))) ∧
        ringKrullDim (MvPolynomial (Fin n) F ⧸
            (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F))) =
          ringKrullDim (MRing (PBlk n) ⧸ W) ∧
        ∀ i : Fin n, ((X i : MvPolynomial (Fin n) F) ∈
            (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) ↔
          (X ⟨(), i⟩ : MRing (PBlk n)) ∈ W)

end ObjectsChow

end GroundTheory.Heights₂.Heights
