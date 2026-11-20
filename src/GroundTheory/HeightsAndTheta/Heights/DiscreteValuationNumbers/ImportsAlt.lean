import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem EffectiveCase.proof (h₀ : NoCommonComponentCase.Statement.{u}) (h₁ : CommonFactorInduction.Statement.{u}) :
    EffectiveCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ

  suffices H : ∀ n : ℕ, ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
      ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
      ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
      (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
      commonExcess ϖ P f g s = n → ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L by
    intro K _ _ ι _ P d hP b f g hD c s hs hsP hH L
    exact H _ K ι P d hP b f g hD c s hs hsP hH rfl L
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K _ _ ι _ P d hP b f g hD c s hs hsP hH hn L
    by_cases hcom : ∃ G, (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G ∧ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) ≠ 0 ∧ ratDiv P f g G ≠ 0
    · refine h₁ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hcom ?_ L
      intro K' _ _ ι' _ P' d' hP' b' f' g' hD' c' s' hs' hsP' hH' hlt L'
      exact ih _ (hn ▸ hlt) K' ι' P' d' hP' b' f' g' hD' c' s' hs' hsP' hH' rfl L'
    · refine h₀ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH (fun G hG hsG => ?_) L
      by_contra hDG
      exact hcom ⟨G, hG, hsG, hDG⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
