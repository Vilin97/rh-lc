module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpFibreDegree.proof (ha : HomLocRingLocal.Statement.{u}) (hb : DivCycleHomLoc.Statement.{u})
    (hc : FiniteBirationalLength.Statement.{u}) (hd : BlowUpFibreSemilocal.Statement.{u}) :
    BlowUpFibreDegree.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hdiv
  have hsupp : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hdiv (by unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle; rw [dite_eq_right h])
  have hWp : W.IsPrime := hsupp.1.1.1
  have := hP.multiProj.isPrime
  obtain ⟨i, hi⟩ := powMonomial_not_mem hWp hsupp.2 c
  have hg : IsMultiHomog (powMonomial c i : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) c := isMultiHomog_powMonomial c i
  have hz : algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P)) (Ideal.Quotient.mk P x) /
      algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P))
        (Ideal.Quotient.mk P (powMonomial c i)) ∈ homLocRing P W :=
    Subring.subset_closure ⟨c, x, _, hx, hg, hi, rfl⟩
  obtain ⟨hloc, hnoeth, hdim⟩ := ha O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2
  have := hloc
  have := hnoeth
  obtain ⟨B, _, _, _, hfin, hinj, hrank, e, he⟩ :=
    hd O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hsupp.1 hsupp.2 _ hg hi hz
  have hz0 : (⟨_, hz⟩ : homLocRing P W) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun w : homLocRing P W => (w : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P))) h0
    simp only [ZeroMemClass.coe_zero] at h1
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact hxP (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P))) (by rw [h, map_zero])))
    · exact hi (hsupp.1.1.2 (Ideal.mem_sup_left (Ideal.Quotient.eq_zero_iff_mem.mp
        ((IsFractionRing.injective _ (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ P))) (by rw [h, map_zero])))))
  obtain ⟨hfinite, hlen⟩ := hc (homLocRing P W) B hdim hinj hrank _ hz0
  have hmult := hb O K ι P hP.multiProj c x hx hxP W hsupp.1 hsupp.2 _ hg hi hz
  have hdivW : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ) = ((multAt (P ⊔ Ideal.span {x}) W).toNat : ℤ) := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
    rw [dite_eq_left hsupp]
  have := Fintype.ofFinite {𝔫 : Ideal B // 𝔫.IsMaximal}

  have hterm : ∀ 𝔫 : {𝔫 : Ideal B // 𝔫.IsMaximal},
      (have := 𝔫.2.isPrime
       Module.length (Localization.AtPrime 𝔫.1)
         (Localization.AtPrime 𝔫.1 ⧸ Ideal.span {algebraMap B (Localization.AtPrime 𝔫.1)
           (algebraMap (homLocRing P W) B ⟨_, hz⟩)})) * (𝔫.1.inertiaDeg (homLocRing P W) : ℕ∞) =
        (((((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) (e 𝔫) : ℤ).1).toNat * specialRelDeg (e 𝔫).1 : ℕ) : ℕ∞) := by
    intro 𝔫
    rw [(he 𝔫).1, (he 𝔫).2, Nat.cast_mul]
  rw [finsum_congr hterm, finsum_eq_sum_of_fintype, ← Nat.cast_sum] at hlen
  rw [hdivW, hmult, hlen, ENat.toNat_natCast, Nat.cast_sum]

  classical
  let p : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) → Prop := fun W' =>
    W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' ∧
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
  have hite : ∀ W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)),
      (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W' : ℤ) * (specialRelDeg W' : ℤ) else 0) =
      ∑ᶠ (_ : p W'), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W' : ℤ) * (specialRelDeg W' : ℤ) := by
    intro W'
    rw [finsum_eq_if]
    by_cases hc' : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
    · by_cases hp : p W'
      · rw [if_pos hc', if_pos hp]
      · rw [if_pos hc', if_neg hp]
        have h0 : ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W' : ℤ) = 0 := by
          unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          rw [dite_eq_right]
          exact fun h => hp ⟨h.1, h.2, hc'⟩
        rw [h0, zero_mul]
    · rw [if_neg hc', if_neg (fun h => hc' h.2.2)]
  rw [finsum_congr hite, ← finsum_subtype_eq_finsum_cond p,
    ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun 𝔫 _ => ?_
  have h0 : 0 ≤ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) (e 𝔫) : ℤ).1 := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
    split_ifs <;> positivity
  rw [Nat.cast_mul, Int.toNat_of_nonneg h0]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
