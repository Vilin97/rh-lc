import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def SliceComponents.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u ℓ : Fin n → ℂ),
    IsProjPrime J → (∀ W ∈ ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle J u) W : ℤ))).support, linForm ℓ ∉ W) →
      Set.InjOn (fun W => W ⊔ Ideal.span {linForm ℓ - 1}) (((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle J u) W : ℤ))).support : Set _) ∧
        (fun W => W ⊔ Ideal.span {linForm ℓ - 1}) '' (((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle J u) W : ℤ))).support : Set _) =
          (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u}).minimalPrimes ∧
        ∀ W ∈ ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle J u) W : ℤ))).support,
          localMult (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u})
              (W ⊔ Ideal.span {linForm ℓ - 1}) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle J u) W : ℤ)

end

end GroundTheory.Heights₂.Heights
