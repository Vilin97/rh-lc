import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem divCycle_ne_zero_facts {O : Type u} [CommRing O] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)} (hP : IsMultiHomogIdeal P) {f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι} {e : K → ℕ}
    (hf : IsMultiHomog f e) {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)} (h : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) ≠ 0) :
    W.IsPrime ∧ IsRelevant W ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at h
  split_ifs at h with hW
  · obtain ⟨hmin, hrel⟩ := hW
    refine ⟨hmin.1.1, hrel, le_trans le_sup_left hmin.1.2, ?_⟩
    exact MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P f e hP hf) hmin
  · exact absurd rfl h

theorem LeftTermSupport.proof : LeftTermSupport.Statement.{u} := by
  intro O _ _ _ ϖ K _ _ ι _ P hP b f g hD c s hs G U hU
  by_contra hne
  apply hU
  have hG : ratDiv P f g G ≠ 0 := left_ne_zero_of_mul hne
  have hU' : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle G s) U : ℤ) ≠ 0 := right_ne_zero_of_mul hne
  have hϖG : (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G := hD.vertical G hG
  obtain ⟨bf, bg, hf, hg, -⟩ := hD.degrees
  have hGfacts : P ≤ G ∧ IsMultiHomogIdeal G := by
    have : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) G : ℤ) ≠ 0 ∨ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g) G : ℤ) ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hG (by unfold ratDiv; rw [h.1, h.2, sub_zero])
    rcases this with h | h
    · exact (divCycle_ne_zero_facts hP hf h).2.2
    · exact (divCycle_ne_zero_facts hP hg h).2.2
  obtain ⟨hUp, hUr, hGU, hUm⟩ := divCycle_ne_zero_facts hGfacts.2 hs hU'
  exact ⟨hUp, hUm, hUr, hGU hϖG, le_trans hGfacts.1 hGU⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
