import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceSectionTailMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle W u') W : ℤ))).support, linForm ℓ ∉ P) →
      ∀ P ∈ ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle W u') W : ℤ))).support,
        Tendsto (fun k => varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e (fun x => 1 - sliceCut h k x)
          (fun _ x => Real.log (h.dualNorm x))) atTop (𝓝 0)

end

end GroundTheory.Heights₂.Heights
