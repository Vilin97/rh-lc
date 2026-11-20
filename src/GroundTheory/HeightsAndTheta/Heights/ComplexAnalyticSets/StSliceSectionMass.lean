import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LineInhabitant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceSectionMass.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u ℓ : Fin n → ℂ),
    IsProjPrime J → IsChowForm J (e + 2) F → linForm u ∉ J → linForm ℓ ∉ J →
    (∀ W ∈ ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle J u) W : ℤ))).support, linForm ℓ ∉ W) →
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ => 1)
          (fun _ x => Real.log (h.dualNorm x)) =
        ∑ W ∈ ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle J u) W : ℤ))).support, ((((ReciprocityTheory.ChartRestriction.G.Geo.divCycle J u) W : ℤ) : ℕ) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (fun _ => 1)
            (fun _ x => Real.log (h.dualNorm x))

end

end GroundTheory.Heights₂.Heights
