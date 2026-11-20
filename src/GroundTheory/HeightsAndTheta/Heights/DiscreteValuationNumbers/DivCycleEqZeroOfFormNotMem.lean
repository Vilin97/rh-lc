import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_nonneg (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) :
    0 ≤ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  split_ifs <;> simp

theorem divCycle_eq_zero_of_form_not_mem (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) {x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι} {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)}
    (hx : x ∉ W) : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ) = 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  rw [dite_eq_right]
  exact fun h => hx (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end

theorem ExcessPositive.proof : ExcessPositive.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP ⟨G, hϖG, hsG, hDG⟩
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hGdef : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant G := by
    by_contra h
    exact hsG (by unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle; rw [dite_eq_right h])
  have hGp : G.IsPrime := hGdef.1.1.1
  have hPG : P ≤ G := le_sup_left.trans hGdef.1.1.2
  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGp hPG hGdef.2
  have huP : u ∉ P := fun h => huG (hPG h)
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have hvP : v ∉ P := by
    intro hv
    have h1 : u * f ∈ P := by
      have h2 := P.add_mem huv (P.mul_mem_right g hv)
      rwa [sub_add_cancel] at h2
    exact (hPp.mem_or_mem h1).elim huP hfP
  have hcyc : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (u * f)) G : ℤ) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (v * g)) G : ℤ) :=
    congrFun (divCycle_congr_of_sub_mem huv) G
  have huf := congrFun (DivCycleMul.proof O K ι P u f hPp huP hfP) G
  have hvg := congrFun (DivCycleMul.proof O K ι P v g hPp hvP hgP) G
  simp only [Pi.add_apply] at huf hvg
  have hu0 := divCycle_eq_zero_of_form_not_mem P huG
  have hv0 := divCycle_nonneg P v G
  have hs0 := divCycle_nonneg P s G
  have hDpos : 0 < ratDiv P f g G := by
    unfold ratDiv at hDG ⊢
    omega
  have hprod : 0 < (((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) * ratDiv P f g G).toNat := by
    have : 0 < ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) * ratDiv P f g G := mul_pos (lt_of_le_of_ne hs0 (Ne.symm hsG)) hDpos
    omega

  have hfin := DivCycleFiniteSupport.proof.{u} O K ι P s
  have hbdd : BddAbove (Set.range fun G' : {G' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) // (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G'} =>
      (((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G'.1 : ℤ) * ratDiv P f g G'.1).toNat) := by
    apply Set.Finite.bddAbove
    apply ((hfin.image fun G' => (((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G' : ℤ) * ratDiv P f g G').toNat).insert 0).subset
    rintro _ ⟨G', rfl⟩
    by_cases h : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G'.1 : ℤ) = 0
    · left
      simp [h]
    · right
      exact ⟨G'.1, h, rfl⟩
  exact lt_of_lt_of_le hprod (le_ciSup hbdd ⟨G, hϖG⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
