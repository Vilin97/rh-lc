import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Chart

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

def chartSubst (a : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) : (Σ o, extIdx ι J o) → Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)
  | ⟨none, j⟩ => Polynomial.C (a j) * Polynomial.X
  | ⟨some k, i⟩ => Polynomial.C (X ⟨k, i⟩)

theorem aeval_chartSubst_liftForm (a : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (p : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) :
    aeval (chartSubst a) (liftForm p) = Polynomial.C p := by
  have e : (aeval (chartSubst a)).comp (liftForm : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι →ₐ[R] ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (extIdx ι J)) =
      Polynomial.CAlgHom := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [liftForm, chartSubst]
  exact DFunLike.congr_fun e p

theorem aeval_chartSubst_mem_of_mem_blowUpOf {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)} (hP : P.IsPrime)
    {u a : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι} {u₀ g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι} (hg : g ∉ P) (h : ∀ j, u₀ * u j - g * a j ∈ P)
    {F : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (extIdx ι J)} (hF : F ∈ blowUpOf P u) :
    aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι →+* Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) P := by
  let π := Polynomial.mapRingHom (Ideal.Quotient.mk P)
  have key : (Polynomial.compRingHom (Polynomial.C (Ideal.Quotient.mk P g) * Polynomial.X)).comp
        (π.comp (aeval (R := R) (chartSubst a)).toRingHom) =
      (Polynomial.compRingHom (Polynomial.C (Ideal.Quotient.mk P u₀) * Polynomial.X)).comp
        (aeval (R := R) (blowUpSubst P u)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [π, Polynomial.compRingHom]
      rfl
    · rintro ⟨_ | k, i⟩
      · have e : Ideal.Quotient.mk P (u₀ * u i) = Ideal.Quotient.mk P (g * a i) :=
          Ideal.Quotient.eq.mpr (h i)
        simp only [map_mul] at e
        simp [π, chartSubst, blowUpSubst, Polynomial.compRingHom]
        have e' : Polynomial.C (Ideal.Quotient.mk P (a i)) * Polynomial.C (Ideal.Quotient.mk P g) =
            Polynomial.C (Ideal.Quotient.mk P (u i)) * Polynomial.C (Ideal.Quotient.mk P u₀) := by
          rw [← Polynomial.C_mul, ← Polynomial.C_mul, mul_comm (Ideal.Quotient.mk P (u i)), e, mul_comm]
        rw [← mul_assoc, ← mul_assoc, e']
      · simp [π, chartSubst, blowUpSubst, Polynomial.compRingHom]
  have hF' : π (aeval (chartSubst a) F) = 0 := by
    have e := DFunLike.congr_fun key F
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at e
    rw [show aeval (blowUpSubst P u) F = 0 from RingHom.mem_ker.mp hF, map_zero] at e
    have hg' : Ideal.Quotient.mk P g ∈ nonZeroDivisors (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    exact (Polynomial.comp_C_mul_X_eq_zero_iff hg').mp e
  have hk : aeval (chartSubst a) F ∈ RingHom.ker π := hF'
  rwa [Polynomial.ker_mapRingHom, Ideal.mk_ker] at hk

theorem mem_of_aeval_chartSubst_mem {a : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι} {H : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (extIdx ι J))}
    (hH : H.IsPrime) {P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)} (hP'H : P' ≤ H.comap (liftForm (J := J))) (j₀ : J)
    (ha : liftForm (a j₀) ∉ H)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ H)
    {F : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (extIdx ι J)}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι →+* Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) P') :
    F ∈ H := by
  let L := FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (extIdx ι J) ⧸ H)
  let q : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (extIdx ι J) →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk H)
  have hq : ∀ y, q y = 0 ↔ y ∈ H := by
    intro y
    simp only [q, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ L), Ideal.Quotient.eq_zero_iff_mem]
  have ha' : q (liftForm (a j₀)) ≠ 0 := fun h0 => ha ((hq _).mp h0)
  let ε : Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) →+* L :=
    Polynomial.eval₂RingHom (q.comp (liftForm (J := J) : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι →ₐ[R] _).toRingHom)
      (q (newVar j₀) / q (liftForm (a j₀)))
  have key : ε.comp (aeval (R := R) (chartSubst a)).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ε, liftForm_C]
    · rintro ⟨_ | k, i⟩
      · have h1 := (hq _).mpr (hrel i)
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
        simp only [ε, chartSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [← mul_div_assoc, div_eq_iff ha', mul_comm]
        exact h1.symm
      · simp [ε, chartSubst, liftForm]
  have hε : Ideal.map (Polynomial.C : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι →+* Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) P' ≤ RingHom.ker ε := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [ε, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    exact (hq _).mpr (hP'H hp)
  have h2 := RingHom.mem_ker.mp (hε hF)
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [h3] at h2
  exact (hq F).mp h2

end Chart

theorem BlowUpStrictTransform.proof : BlowUpStrictTransform.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP e m H hϖH hH
  set Q := blowUpOf P (blowUpGens s g f m e) with hQ
  have hPp : P.IsPrime := hP.multiProj.isPrime

  obtain ⟨x, hx, hHmin⟩ : ∃ x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι)),
      (x = liftForm s ∨ x = newVar none) ∧ H ∈ (Q ⊔ Ideal.span {x}).minimalPrimes := by
    have hm : ∀ {F}, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle Q F) H : ℤ) ≠ 0 → H ∈ (Q ⊔ Ideal.span {F}).minimalPrimes := by
      intro F hF
      unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle at hF
      split_ifs at hF with hW
      · exact hW.1
      · exact absurd rfl hF
    rcases hH with hH | hH
    · exact ⟨_, Or.inl rfl, hm hH⟩
    · exact ⟨_, Or.inr rfl, hm hH⟩
  obtain ⟨hHp, hQH, hHrel⟩ : H.IsPrime ∧ Q ≤ H ∧ IsRelevant H := by
    rcases hH with hH | hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
    · exact le_and_isRelevant_of_divCycle_ne_zero hH
  have mnm : ∀ {y z}, y ∉ H → z ∉ H → y * z ∉ H := fun hy hz hyz => (hHp.mem_or_mem hyz).elim hy hz
  have hxH : x ∈ H := hHmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  set H₀ := H.comap (liftForm (J := BlowUpIdx ι)) with hH₀
  obtain ⟨hH₀p, hPH₀, hrel₀, -⟩ := comap_liftForm_facts hHp hQH hHrel
  have hϖH₀ : (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖH

  obtain ⟨u₀, v₀, hu, hv, h⟩ := hD.unit_off_special H₀ hH₀p hPH₀ hrel₀ hϖH₀
  obtain ⟨i, hpm, hYi, -⟩ := blowUp_offSpecial hPp e hD.den_not_mem hHp hQH hHrel (u₀ := u₀) hv h
  set a := blowUpCof s m e u₀ v₀ with ha_def
  have haS : liftForm (a (some (some i))) ∉ H := by
    show liftForm (v₀ * powMonomial e i) ∉ H
    rw [map_mul]; exact mnm hv hpm
  have hrelH : ∀ j, newVar j * liftForm (a (some (some i))) -
      newVar (some (some i)) * liftForm (a j) ∈ H :=
    fun j => hQH (blowUpCof_relation hPp e hD.den_not_mem h j _)

  have hsH₀ : s ∈ H₀ := by
    rcases hx with rfl | rfl
    · exact hxH
    · have h3 := H.sub_mem (H.mul_mem_right (liftForm (a (some (some i)))) hxH) (hrelH none)
      rw [sub_sub_cancel] at h3
      have h4 : liftForm (u₀ * s) ∈ H := (hHp.mem_or_mem h3).resolve_left hYi
      rw [map_mul] at h4
      exact (hHp.mem_or_mem h4).resolve_left hu

  have hmin₀ : H₀ ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
    refine ⟨⟨hH₀p, sup_le hPH₀ ((Ideal.span_singleton_le_iff_mem _).mpr hsH₀)⟩,
      fun P' hP' hP'H₀ => ?_⟩
    have := hP'.1
    have hsP' : s ∈ P' := hP'.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
    let Q' := (Ideal.map (Polynomial.C : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι →+* Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) P').comap
      (aeval (R := O) (chartSubst a))
    have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
    have hQQ' : Q ⊔ Ideal.span {x} ≤ Q' := by
      refine sup_le (fun F hF => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      · exact Ideal.map_mono (le_sup_left.trans hP'.2)
          (aeval_chartSubst_mem_of_mem_blowUpOf hPp hD.den_not_mem (fun j => blowUpCof_spec e h j) hF)
      · rw [Ideal.mem_comap]
        rcases hx with rfl | rfl
        · rw [aeval_chartSubst_liftForm]
          exact Ideal.mem_map_of_mem _ hsP'
        · simp only [newVar, aeval_X, chartSubst]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (P'.mul_mem_left _ hsP'))
    have hQ'H : Q' ≤ H := fun F hF => mem_of_aeval_chartSubst_mem hHp hP'H₀ _ haS hrelH hF
    have hHQ' := hHmin.2 ⟨hQ'p, hQQ'⟩ hQ'H
    intro p hp
    have h5 : Polynomial.C p ∈ Ideal.map (Polynomial.C : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι →+* Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) P' := by
      rw [← aeval_chartSubst_liftForm a p]
      exact hHQ' hp
    simpa using Ideal.mem_map_C_iff.mp h5 0

  have := hH₀p
  unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  rw [dite_eq_left ⟨hmin₀, hrel₀⟩]
  have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {s}) H₀ hmin₀
  have hnz : multAt (P ⊔ Ideal.span {s}) H₀ ≠ 0 := by
    unfold multAt
    rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    intro hs
    obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hr0
    exact hr (hmin₀.1.2 hr0)
  have htn : (multAt (P ⊔ Ideal.span {s}) H₀).toNat ≠ 0 :=
    fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
  exact_mod_cast htn

end

end GroundTheory.Heights₂.Heights.NumbersDVR
