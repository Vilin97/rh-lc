import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarSurj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

set_option maxHeartbeats 400000 in

theorem ConeVarSurj.proof : ConeVarSurj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  classical
  intro z
  set L := FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)
  let π : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι → L := fun x => algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) L (Ideal.Quotient.mk P x)
  have hπ : ∀ x, x ∉ P → π x ≠ 0 := fun x hx => by
    simp only [π, Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  let U : (K → ℕ) → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι := fun d => ∏ k, (X ⟨k, v k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ^ d k
  have hUh : ∀ d, IsMultiHomog (U d) d := fun d => by
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X _ _ _).pow _)
    have hd : ∑ k, d k • blockWeight ι ⟨k, v k⟩ = d := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hd] at this
    exact this
  have hUW : ∀ d, U d ∉ W := fun d =>
    W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hv k) _
  let comp : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι → (K → ℕ) → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι := fun h d =>
    weightedHomogeneousComponent (blockWeight ι) d h
  let c : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι → (K → ℕ) → degZeroLoc P {W} := fun h d =>
    ⟨π (comp h d) / π (U d), div_mem_degZeroLoc P {W}
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (hUh d) (fun h' => hUW d (hPW h')) (by rintro _ rfl; exact hUW d)⟩
  let D : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι → Finset (K → ℕ) := fun h => h.support.image (Finsupp.weight (blockWeight ι))
  have hsum : ∀ h, ∑ d ∈ D h, comp h d = h := fun h => by
    rw [← finsum_eq_sum_of_support_subset _ (s := D h) (fun d hd => by
      by_contra hd'
      exact hd (weightedHomogeneousComponent_eq_zero_of_notMem _ h d hd'))]
    exact sum_weightedHomogeneousComponent (blockWeight ι) h
  let Q : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι → MvPolynomial K (degZeroLoc P {W}) := fun h =>
    ∑ d ∈ D h, monomial (Finsupp.equivFunOnFinite.symm d) (c h d)
  have hQ : ∀ h, coneVarMap P W hPW v (Q h) =
      algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h) := fun h => by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← hsum h, map_sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coneVarMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, degZeroLoc.algebraMap_cone_coe, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Finsupp.coe_equivFunOnFinite_symm]
    have hU : ∏ k, algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P) L (Ideal.Quotient.mk P (X ⟨k, v k⟩)) ^ d k =
        π (U d) := by
      simp [π, U, map_prod, map_pow]
    rw [hU]
    exact div_mul_cancel₀ _ (hπ _ fun h' => hUW d (hPW h'))
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (W.primeCompl.map (Ideal.Quotient.mk P)) z
  obtain ⟨g, hg, hgs⟩ := Submonoid.mem_map.mp s.2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨d, hdD, hdW⟩ : ∃ d ∈ D g, comp g d ∉ W := by
    by_contra hne
    push Not at hne
    exact hg (hsum g ▸ W.sum_mem hne)
  refine ⟨Q f, Q g, Finsupp.equivFunOnFinite.symm d, ?_, ?_⟩
  · have hcoeff : (Q g).coeff (Finsupp.equivFunOnFinite.symm d) = c g d := by
      simp only [Q, coeff_sum, coeff_monomial, EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.sum_ite_eq', if_pos hdD]
    rw [hcoeff]
    refine isUnit_iff_exists_inv.mpr ⟨⟨π (U d) / π (comp g d), div_mem_degZeroLoc P {W} (hUh d)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (fun h' => hdW (hPW h'))
      (by rintro _ rfl; exact hdW)⟩, Subtype.ext ?_⟩
    simp only [c, Subalgebra.coe_mul, Subalgebra.coe_one]
    rw [div_mul_div_cancel₀ (hπ _ fun h' => hUW d (hPW h')), div_self (hπ _ fun h' => hdW (hPW h'))]
  · rw [hQ, hQ, hgs]
    exact hxs

end

end GroundTheory.Heights₂.Heights.FieldNumbers
