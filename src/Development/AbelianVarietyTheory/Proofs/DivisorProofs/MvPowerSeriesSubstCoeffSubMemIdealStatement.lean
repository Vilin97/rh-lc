module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesSubstCoeffSubMemIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_subst_coeff_sub_mem_ideal :
    ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ]
      (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) →
      (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) →
      ∀ (m : ℕ) (c : MvPowerSeries σ Q),
        (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) →
        ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N,
          coeff w (MvPowerSeries.subst (QLog.up (Q := Q) u) c) -
            coeff w (MvPowerSeries.subst (QLog.up (Q := Q) ℓ) c) = algebraMap B Q r := by
  intro B Q σ τ _ _ _ _ N u ℓ hu hlin m c hc w hw
  have hℓ : ∀ s, constantCoeff (ℓ s) = 0 := fun s => by
    simpa only [coeff_zero_eq_constantCoeff_apply, hu s] using (hlin s 0 (by simp)).symm
  have horder : ∀ s, (2 : ℕ∞) ≤ (u s - ℓ s).order := fun s =>
    nat_le_order (n := 2) fun β hβ => by
      rw [map_sub, hlin s β (by omega), sub_self]
  have huSubst : HasSubst (QLog.up (Q := Q) u) :=
    hasSubst_of_constantCoeff_zero fun s => by simp [QLog.up, hu s]
  have hℓSubst : HasSubst (QLog.up (Q := Q) ℓ) :=
    hasSubst_of_constantCoeff_zero fun s => by simp [QLog.up, hℓ s]
  have hpow (s : σ) (n : ℕ) : (n : ℕ∞) + 1 ≤ (u s ^ n - ℓ s ^ n).order := by
    have h := GlobalTheory.OrderProductDifference.order_prod_sub_prod (Finset.range n)
      (fun _ => u s) (fun _ => ℓ s) (fun _ => 1)
      (fun _ _ => one_le_order_iff_constCoeff_eq_zero.mpr (hu s))
      (fun _ _ => one_le_order_iff_constCoeff_eq_zero.mpr (hℓ s))
      (fun _ _ => by simpa [one_add_one_eq_two] using horder s)
    simpa [Finset.prod_const] using h
  rw [coeff_subst huSubst, coeff_subst hℓSubst,
    ← finsum_sub_distrib (coeff_subst_finite huSubst c w) (coeff_subst_finite hℓSubst c w)]
  refine finsum_induction (fun x : Q => ∃ r ∈ N, x = algebraMap B Q r)
    ⟨0, N.zero_mem, by simp⟩
    (fun x y ⟨r, hr, hx⟩ ⟨t, ht, hy⟩ => ⟨r + t, N.add_mem hr ht, by rw [hx, hy, map_add]⟩)
    fun α => ?_
  have hprod (v : σ → MvPowerSeries τ B) :
      (α.prod fun s e => QLog.up (Q := Q) v s ^ e) =
        MvPowerSeries.map (algebraMap B Q) (α.prod fun s e => v s ^ e) := by
    simp only [QLog.up, Finsupp.prod, map_prod, map_pow]
  rw [hprod u, hprod ℓ, coeff_map, coeff_map, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub,
    ← map_sub]
  by_cases h : α.degree < m
  · obtain ⟨b, hb, hcb⟩ := hc α h
    exact ⟨b * _, N.mul_mem_right _ hb, by rw [hcb, map_mul]⟩
  · have hmono : (α.degree : ℕ∞) + 1 ≤
        ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e).order := by
      rw [Finsupp.degree_apply]
      push_cast
      exact GlobalTheory.OrderProductDifference.order_prod_sub_prod α.support
        (fun s => u s ^ α s) (fun s => ℓ s ^ α s) α
        (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hu s))
        (fun s _ => le_order_pow_of_constantCoeff_eq_zero _ (hℓ s))
        (fun s _ => hpow s (α s))
    have hdegree : w.degree < α.degree + 1 := by omega
    have hzero : coeff w ((α.prod fun s e => u s ^ e) - α.prod fun s e => ℓ s ^ e) = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hdegree) hmono)
    exact ⟨0, N.zero_mem, by rw [hzero, map_zero, mul_zero]⟩
