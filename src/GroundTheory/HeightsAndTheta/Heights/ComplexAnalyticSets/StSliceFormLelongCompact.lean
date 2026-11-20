import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormLelong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceFormLelongCompact.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ) (u' ℓ : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ),
    IsProjPrime W → IsChowForm W (e + 2) F → linForm u' ∉ W → linForm ℓ ∉ W →
    (∀ P ∈ ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle W u') W : ℤ))).support, linForm ℓ ∉ P) →
    SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) f → HasCompactSupport f →
      Tendsto (fun ε => varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) f
          (vecCons (fsLogReg h u' ε) fun _ x => Real.log (h.dualNorm x))) (𝓝[>] 0)
        (𝓝 (∑ P ∈ ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle W u') W : ℤ))).support, ((((ReciprocityTheory.ChartRestriction.G.Geo.divCycle W u') P : ℤ) : ℕ) : ℝ) *
            varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e f (fun _ x => Real.log (h.dualNorm x)) -
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) f (fun _ x => Real.log (h.dualNorm x))))

end

end GroundTheory.Heights₂.Heights
