module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicFrobeniusSystemContinuationOpenDisc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc
open PowerSeries GlobalTheory.Cyc.Cont in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicFrobenius_system_continuation_open_disc : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : FinExt l) (s r n M : ℕ) [NeZero n], 1 ≤ s → ∀ (t τ : PowerSeries ↥LL.1), PowerSeries.constantCoeff t = 0 → (1 + PowerSeries.X) * PowerSeries.derivative t = 1 → XX l ↥LL.1 s * τ = t → ∀ (U : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥LL.1)) (Pm : ZMod n → Matrix (Fin r) (Fin r) (PowerSeries ↥(OL LL))) (Cm : ZMod n → Matrix (Fin r) (Fin r) ↥LL.1) (ρ : ℝ), 0 < ρ → (∀ i, QQ l ↥LL.1 s ^ M • U i = (Pm i).map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) * (U (i - 1)).map (phi l ↥LL.1) * (Cm i).map PowerSeries.C) → (∀ i a b, (∀ r : ℝ, 0 < r → r < ρ → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0))) → ∀ i a b, (∀ r : ℝ, 0 < r → r < 1 → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (τ ^ M * U i a b) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) := by
  intro l hl LL s r n M _ hs t τ h0 h1 hτ U Pm Cm ρ hρ hU hc i a b x hx hx1
  have hphi : phi l ↥LL.1 t = (l : (↥LL.1)⟦X⟧) * t := by
    have hs : HasSubst (cyc l ↥LL.1 (l : ℤ_[l])) := HasSubst.of_constantCoeff_zero' (cyc_const l ↥LL.1 _)
    have hne : (1 + X : (↥LL.1)⟦X⟧) ≠ 0 := fun h => by simp [h] at h1
    have hl1 : l - 1 + 1 = l := Nat.sub_add_cancel hl.out.one_le
    apply derivative.ext
    · have e : derivative (phi l ↥LL.1 t) = phi l ↥LL.1 (derivative t) * derivative ((1 + X) ^ l - 1) := by
        rw [phi, act_apply, act_apply, derivative_subst hs, cyc_natCast]
      have e2 := congrArg (phi l ↥LL.1) h1
      rw [map_mul, map_add (f := _), map_one, Cont.phi_X, add_sub_cancel] at e2
      have e3 : derivative ((1 + X : (↥LL.1)⟦X⟧) ^ l - 1) = (l : (↥LL.1)⟦X⟧) * (1 + X : (↥LL.1)⟦X⟧) ^ (l - 1) := by
        simp [Derivation.leibniz_pow]
      have e4 : derivative ((l : (↥LL.1)⟦X⟧) * t) = (l : (↥LL.1)⟦X⟧) * derivative t := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
      apply mul_left_cancel₀ hne
      have e5 : (1 + X : (↥LL.1)⟦X⟧) ^ l = (1 + X) ^ (l - 1) * (1 + X) := by rw [← pow_succ, hl1]
      rw [e5] at e2
      rw [e, e3, e4]
      linear_combination (l : (↥LL.1)⟦X⟧) * e2 - (l : (↥LL.1)⟦X⟧) * h1
    · obtain ⟨a, rfl⟩ := X_dvd_iff.2 h0
      simp [Cont.phi_X]
  have hlog : ∀ (a : (↥LL.1)⟦X⟧), (1 + X) * derivative (X * a) = 1 →
      ∀ r : ℝ, 0 < r → r < 1 → ∃ c, Bd r c a := by
    intro a h1 r hr hr1
    have hd : ∀ k, ‖coeff k (derivative (X * a))‖ = 1 := by
      intro k
      induction k with
      | zero =>
        have := congrArg (coeff 0) h1
        rw [add_mul, one_mul, map_add (f := _), coeff_zero_X_mul, add_zero, coeff_one, ite_eq_left rfl] at this
        rw [this, norm_one]
      | succ k ih =>
        have := congrArg (coeff (k + 1)) h1
        rw [add_mul, one_mul, map_add (f := _), coeff_succ_X_mul, coeff_one, ite_eq_right k.succ_ne_zero] at this
        rw [eq_neg_of_add_eq_zero_left this, norm_neg, ih]
    have hb : ∀ k, ‖coeff k a‖ ≤ k + 1 := by
      intro k
      have h := hd k
      rw [coeff_derivative, coeff_succ_X_mul, norm_mul, ← Nat.cast_succ, norm_nat] at h
      have h2 := inv_le_norm_nat l (k + 1) k.succ_ne_zero
      calc ‖coeff k a‖ ≤ ‖coeff k a‖ * (((k + 1 : ℕ) : ℝ) * ‖((k + 1 : ℕ) : ℤ_[l])‖) :=
            le_mul_of_one_le_right (norm_nonneg _) h2
        _ = k + 1 := by rw [mul_left_comm, h]; simp
    refine bd_of_tendsto (squeeze_zero (fun k => by positivity)
      (fun k => mul_le_mul_of_nonneg_right (hb k) (by positivity)) ?_)
    simpa [add_mul] using (tendsto_self_mul_const_pow_of_lt_one hr.le hr1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1)
  have hX : XX l ↥LL.1 s ≠ 0 := fun h => by
    rw [h, zero_mul] at hτ
    simp [← hτ] at h1
  have hl0 : (l : ↥LL.1) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have htau (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : ∃ c, Bd r c τ := by
    have hj : ∀ j : ℕ, (phi l ↥LL.1 ^ j) t = (l : (↥LL.1)⟦X⟧) ^ j * t := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', AlgHom.mul_apply, ih, map_mul, map_pow, map_natCast, hphi]
        ring
    obtain ⟨a, ha⟩ := X_dvd_iff.2 h0
    have h2 := hj (s - 1)
    conv_lhs at h2 => rw [ha, map_mul, phi_pow_X]
    have h3 : (phi l ↥LL.1 ^ (s - 1)) a = (l : (↥LL.1)⟦X⟧) ^ (s - 1) * τ := by
      apply mul_left_cancel₀ hX
      rw [mul_left_comm, hτ, ← h2, XX]
    have h4 : τ = C (((l : ↥LL.1) ^ (s - 1))⁻¹) * (phi l ↥LL.1 ^ (s - 1)) a := by
      rw [h3, ← mul_assoc, ← map_natCast (C (R := ↥LL.1)), ← map_pow, ← map_mul,
        inv_mul_cancel₀ (pow_ne_zero _ hl0), map_one, one_mul]
    rw [h4]
    exact ex_mul hr ⟨_, bd_C r _⟩ (ex_phi_pow l LL _ hr hr1 (hlog a (ha ▸ h1) r hr hr1))
  have hQ : QQ l ↥LL.1 s * phi l ↥LL.1 τ = (l : (↥LL.1)⟦X⟧) * τ := by
    apply mul_left_cancel₀ hX
    rw [← mul_assoc, ← (XX_QQ_properties l _ s hs).1, ← map_mul, hτ, hphi, ← hτ]
    ring
  have hinv : C (((l : ↥LL.1) ^ M)⁻¹) * (l : (↥LL.1)⟦X⟧) ^ M = 1 := by
    rw [← map_natCast (C (R := ↥LL.1)), ← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hl0), map_one]
  obtain ⟨y, hxy, hy1⟩ := exists_between hx1
  have key := continuation_abstract (phi l ↥LL.1) (phi_X_const l _) _ (inv_lt_one l) (bd_phi_X l LL)
    (fun i : ZMod n => i - 1) (fun i => τ ^ M • U i)
    (fun i => (Pm i).map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)))
    (fun i => C (((l : ↥LL.1) ^ M)⁻¹) • (Cm i).map C)
    (fun z hz hz1 i a b => ⟨1, bd_map _ (norm_OL l LL) hz hz1.le _⟩)
    (fun z hz hz1 i a b => ex_mul hz ⟨_, bd_C z _⟩ ⟨_, bd_C z _⟩)
    (fun i => by
      have e : (τ ^ M • U (i - 1)).map (phi l ↥LL.1) =
          phi l ↥LL.1 τ ^ M • (U (i - 1)).map (phi l ↥LL.1) := by
        ext1 a b
        simp
      simp only [e, Matrix.mul_smul, Matrix.smul_mul, ← hU, smul_smul]
      congr 1
      have : phi l ↥LL.1 τ ^ M * QQ l ↥LL.1 s ^ M = (l : (↥LL.1)⟦X⟧) ^ M * τ ^ M := by
        rw [← mul_pow, mul_comm, hQ, mul_pow]
      linear_combination -(C (((l : ↥LL.1) ^ M)⁻¹)) * this - τ ^ M * hinv)
    (min (ρ / 2) (1 / 2)) (by positivity)
    (fun i a b => by
      have hz : 0 < min (ρ / 2) (1 / 2) := by positivity
      obtain ⟨c, hc'⟩ := htau _ hz ((min_le_right _ _).trans_lt (by norm_num))
      exact ex_mul hz ⟨_, hc'.pow hz M⟩
        (bd_of_tendsto (hc i a b _ hz ((min_le_left _ _).trans_lt (by linarith)))))
    y (hx.trans hxy) hy1 i a b
  obtain ⟨c, hc⟩ := key
  exact hc.tendsto hx hxy
