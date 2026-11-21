module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BabaiCovering
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralTraceNormBounds

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering

open NumberField InfinitePlace Module Submodule TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cover_OE (Z : VS E) :
    ∃ α : 𝓞 E, ‖Z - iota E (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
  set f : ℝ := (Fintype.card (CP E) : ℝ) with hf_def
  have hf : 0 < f := Nat.cast_pos.mpr card_complexPlaces_pos
  set D := dE E with hD_def
  have hD : 0 < D := dE_pos
  set t := D ^ (1 / f) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hD _
  have htinv : D ^ (-(1 / f)) = t⁻¹ := Real.rpow_neg hD.le _
  set lam := Real.sqrt (4 * f * t⁻¹) with hlam_def
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by positivity)
  have hlam2 : lam ^ 2 = 4 * f * t⁻¹ := Real.sq_sqrt (by positivity)
  have trace_ed_local (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
      Algebra.trace ℚ E (integralBasis E i * ed j) = if i = j then 1 else 0 := by
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_right _ (Algebra.traceForm_isSymm ℚ) _ i j
  have trace_int_local (c : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ) (γ : 𝓞 E) :
      ∃ m : ℤ, Algebra.trace ℚ E ((∑ j, c j • ed j) * (γ : E)) = m := by
    obtain ⟨m, hm⟩ : ∃ m : Free.ChooseBasisIndex ℤ (𝓞 E) → ℤ,
        (γ : E) = ∑ i, m i • integralBasis E i := by
      refine ⟨(RingOfIntegers.basis E).repr γ, ?_⟩
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr γ]
      simp [integralBasis_apply]
    have key : ∀ j i, Algebra.trace ℚ E ((c j • ed j) * (m i • integralBasis E i)) =
        if i = j then ((c j * m i : ℤ) : ℚ) else 0 := by
      intro j i
      rw [smul_mul_smul_comm, map_zsmul, mul_comm (ed j), trace_ed_local]
      split_ifs <;> simp
    refine ⟨∑ j, c j * m j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm, Finset.sum_mul_sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [map_sum, key]
    simp [Finset.sum_ite_eq']
  let bdd : Free.ChooseBasisIndex ℤ (𝓞 E) → VS E := fun j => iota E (2 * cc (ed j))
  have inner_bas_bdd (i j : Free.ChooseBasisIndex ℤ (𝓞 E)) :
      inner ℝ (bas E i) (bdd j) = if i = j then 1 else 0 := by
    rw [bas_apply]
    change inner ℝ (iota E (integralBasis E i)) (iota E (2 * cc (ed j))) = _
    rw [inner_iota_eq_trace, cc_mul, cc_cc, cc_two]
    have h2 : integralBasis E i * (2 * ed j) = (2 : ℚ) • (integralBasis E i * ed j) := by
      rw [Algebra.smul_def, map_ofNat]
      ring
    rw [h2, LinearMap.map_smul, trace_ed_local]
    split_ifs <;> norm_num
  have hmin : ∀ x ∈ span ℤ (Set.range bdd), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    let β : E := ∑ j, c j • ed j
    have hxβ : x = iota E (2 * cc β) := by
      rw [← hc]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [bdd, β, cc, map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm]
    have hβ0 : β ≠ 0 := by
      intro hβ
      apply hx0
      rw [hxβ, hβ, cc, map_zero, mul_zero, map_zero]
    have hint : ∀ γ : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (β * γ) = m := by
      intro γ
      exact trace_int_local c γ
    have hN := norm_discr β hβ0 hint
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hnorm : ‖x‖ ^ 2 = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
      rw [hxβ, norm_sq_iota, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [map_mul, norm_mul, cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj,
        map_ofNat, h2n]
      ring
    have hn : (0 : ℝ) < Fintype.card (CP E) := by exact_mod_cast card_complexPlaces_pos
    have hd : 0 < dE E := dE_pos
    have hNinv : (dE E)⁻¹ ≤ |(Algebra.norm ℚ β : ℝ)| := by
      rw [inv_eq_one_div, div_le_iff₀ hd]
      exact hN
    have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (CP E))
      (fun _ => 1 / (Fintype.card (CP E) : ℝ)) (fun w => ‖w.1.embedding β‖ ^ 2)
      (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
      (fun _ _ => by positivity)
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity), prod_norm, ← Finset.mul_sum] at hgm
    have h1 : dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤
        |(Algebra.norm ℚ β : ℝ)| ^ (1 / (Fintype.card (CP E) : ℝ)) := by
      rw [Real.rpow_neg hd.le, ← Real.inv_rpow hd.le]
      exact Real.rpow_le_rpow (inv_nonneg.mpr hd.le) hNinv (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans hgm)
      (by positivity : (0 : ℝ) ≤ 4 * (Fintype.card (CP E) : ℝ))
    have hnormbd : 4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ))) ≤ ‖x‖ ^ 2 := by
      calc 4 * (Fintype.card (CP E) : ℝ) * dE E ^ (-(1 / (Fintype.card (CP E) : ℝ)))
          ≤ 4 * (Fintype.card (CP E) : ℝ) *
            (1 / (Fintype.card (CP E) : ℝ) * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2) := h3
        _ = 4 * ∑ w : CP E, ‖w.1.embedding β‖ ^ 2 := by
          rw [← mul_assoc, mul_assoc 4, mul_one_div_cancel hn.ne', mul_one]
        _ = ‖x‖ ^ 2 := hnorm.symm
    rw [← hf_def, ← hD_def, htinv] at hnormbd
    rw [hlam_def, ← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt hnormbd
  obtain ⟨x, hx, hxb⟩ := BabaiCovering.cover (bas E) bdd inner_bas_bdd lam hlam hmin Z
  obtain ⟨α, rfl⟩ := mem_span_bas hx
  refine ⟨α, ?_⟩
  have hn : (finrank ℝ (VS E) : ℝ) = 2 * f := by
    rw [finrank_VS, (card_CP (E := E)).2]
    push_cast
    ring
  have hfdeg : (fdeg E : ℝ) = f := by rw [← (card_CP (E := E)).1]
  have hrd : rdE E ^ 2 = t := by
    rw [rdE, ← hD_def, (card_CP (E := E)).2, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    push_cast
    rw [← hf_def]
    field_simp
  rw [hn] at hxb
  have hbound : (2 * f) / 4 * ((2 * f) ^ 2 / lam) ^ 2 = 2 * f ^ 4 * t := by
    rw [div_pow, hlam2]
    field_simp
    ring
  rw [hbound] at hxb
  have hB : 0 ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hB (by norm_num : (2 : ℕ) ≠ 0)]
  calc ‖Z - iota E (α : E)‖ ^ 2 ≤ 2 * f ^ 4 * t := hxb
    _ ≤ 4 * f ^ 4 * t := by nlinarith [pow_pos hf 4]
    _ = (2 * (fdeg E : ℝ) ^ 2 * rdE E) ^ 2 := by
        rw [mul_pow, mul_pow, hrd, hfdeg]
        ring

end ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
