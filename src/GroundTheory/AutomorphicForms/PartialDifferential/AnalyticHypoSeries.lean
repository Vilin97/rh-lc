import Mathlib

namespace GroundTheory.Automorphic.Sobolev

open scoped ContDiff NNReal ENNReal Topology
open Set Filter

noncomputable section

section Converse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem hasDerivAt_iteratedFDeriv_line {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    HasDerivAt (fun τ : ℝ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y))
      (iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y)) t := by
  have hz : HasDerivAt (fun τ : ℝ ↦ x₀ + τ • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x₀
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) :=
    (hf.contDiffAt (hs.mem_nhds ht)).differentiableAt_iteratedFDeriv (by
      exact_mod_cast ENat.natCast_lt_top k)
  have h1 := hd.hasFDerivAt.comp_hasDerivAt t hz
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F
    (fun _ ↦ y)).hasFDerivAt.comp_hasDerivAt t h1
  have e : iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y) =
      (fderiv ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) y) (fun _ ↦ y) := by
    rw [iteratedFDeriv_succ_apply_left]; rfl
  rw [e]
  exact h2

theorem iteratedDeriv_line_eq {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) t =
      iteratedFDeriv ℝ k f (x₀ + t • y) (fun _ ↦ y) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    have hU : IsOpen {τ : ℝ | x₀ + τ • y ∈ s} := hs.preimage (by fun_prop)
    have hev : iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) =ᶠ[𝓝 t]
        fun τ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y) := by
      filter_upwards [hU.mem_nhds ht] with τ hτ using ih hτ
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hasDerivAt_iteratedFDeriv_line hs hf x₀ y k ht).deriv

theorem analyticAt_of_norm_iteratedFDeriv_le {f : E → F} {x₀ : E} {r C M : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball x₀ r))
    (hb : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial) :
    AnalyticAt ℝ f x₀ := by sorry































































































































end Converse

section Forward

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall {f : E → F}
    {q : FormalMultilinearSeries ℝ E F} {y : E} {R : ℝ≥0∞} (h : HasFPowerSeriesOnBall f q y R)
    (k : ℕ) : ‖iteratedFDeriv ℝ k f y‖ ≤ k.factorial * ‖q k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [h.iteratedFDeriv_eq_sum_of_completeSpace v]
  calc ‖∑ σ : Equiv.Perm (Fin k), q k (fun i ↦ v (σ i))‖
      ≤ ∑ σ : Equiv.Perm (Fin k), ‖q k (fun i ↦ v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), ‖q k‖ * ∏ i, ‖v i‖ := by
        gcongr with σ
        refine ((q k).le_opNorm _).trans (le_of_eq ?_)
        congr 1
        exact Equiv.prod_comp σ (fun i ↦ ‖v i‖)
    _ = k.factorial * ‖q k‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        ring

theorem nnnorm_changeOrigin_le_of_bound (p : FormalMultilinearSeries ℝ E F) {ρ K : ℝ≥0}
    (hρ : 0 < ρ) (hK : ∀ n, ‖p n‖₊ ≤ K / ρ ^ n) {z : E} (hz : 4 * ‖z‖₊ ≤ ρ)
    (hzr : (‖z‖₊ : ℝ≥0∞) < p.radius) (k : ℕ) :
    ‖p.changeOrigin z k‖₊ ≤ 2 * (K * (2 / ρ) ^ k) := by
  have hsum := p.changeOriginSeries_summable_aux₂ hzr k
  have h1 := p.nnnorm_changeOrigin_le k hzr
  rw [← ENNReal.coe_le_coe] at h1 ⊢
  refine h1.trans ?_
  rw [ENNReal.coe_tsum hsum, ENNReal.tsum_sigma']
  have hterm : ∀ l : ℕ, ∑' _b : { s : Finset (Fin (k + l)) // s.card = l },
      ((‖p (k + l)‖₊ * ‖z‖₊ ^ l : ℝ≥0) : ℝ≥0∞)
      ≤ ((K * (2 / ρ) ^ k * (2⁻¹) ^ l : ℝ≥0) : ℝ≥0∞) := by
    intro l
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
      Fintype.card_fin, nsmul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    have hK' := hK (k + l)
    rw [← NNReal.coe_le_coe] at hK'
    push_cast at hK' ⊢
    have hz' : 4 * ‖z‖ ≤ (ρ : ℝ) := by exact_mod_cast hz
    have hch : ((k + l).choose l : ℝ) ≤ 2 ^ (k + l) := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    have hρ' : (0 : ℝ) < ρ := hρ
    calc ((k + l).choose l : ℝ) * (‖p (k + l)‖ * ‖z‖ ^ l)
        ≤ 2 ^ (k + l) * ((K : ℝ) / (ρ : ℝ) ^ (k + l) * ((ρ : ℝ) / 4) ^ l) := by
          gcongr
          linarith
      _ = (K : ℝ) * (2 / (ρ : ℝ)) ^ k * (2⁻¹) ^ l := by
          have h4 : (4 : ℝ) ^ l = 2 ^ l * 2 ^ l := by rw [← mul_pow]; norm_num
          rw [pow_add, pow_add, div_pow, div_pow, inv_pow, h4]
          field_simp
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  push_cast
  ring

theorem exists_norm_iteratedFDeriv_le_of_analyticAt {f : E → F} {x₀ : E}
    (hf : AnalyticAt ℝ f x₀) :
    ∃ r > 0, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨ρ, hρ0', hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hρ0 : 0 < ρ := ENNReal.coe_pos.1 hρ0'
  obtain ⟨K, hK0, hK⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hρ0 (hρR.trans_le hp.r_le)
  set K' : ℝ≥0 := ⟨K, hK0.le⟩ with hK'def
  have hK' : ∀ n, ‖p n‖₊ ≤ K' / ρ ^ n := fun n ↦ by
    rw [← NNReal.coe_le_coe]; push_cast; exact hK n
  have hρ' : (0 : ℝ) < ρ := hρ0
  refine ⟨(ρ : ℝ) / 4, by positivity, 2 * K, 2 / ρ, by positivity, by positivity,
    fun y hy k ↦ ?_⟩
  set z := y - x₀ with hzdef
  have hz : ‖z‖ < (ρ : ℝ) / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hy
  have hzρ : ‖z‖₊ < ρ := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm]; linarith [norm_nonneg z]
  have hzR : (‖z‖₊ : ℝ≥0∞) < R := lt_trans (by exact_mod_cast hzρ) hρR
  have hq := hp.changeOrigin hzR
  have hxy : x₀ + z = y := by simp [hzdef]
  rw [hxy] at hq
  refine (norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall hq k).trans ?_
  have hb := nnnorm_changeOrigin_le_of_bound p hρ0 hK'
    (z := z) (by rw [← NNReal.coe_le_coe]; push_cast; linarith) (hzR.trans_le hp.r_le) k
  rw [← NNReal.coe_le_coe] at hb
  push_cast at hb
  have hb' : ‖p.changeOrigin z k‖ ≤ 2 * (K * (2 / ρ) ^ k) := hb
  calc (k.factorial : ℝ) * ‖p.changeOrigin z k‖ ≤ k.factorial * (2 * (K * (2 / ρ) ^ k)) := by
        gcongr
    _ = 2 * K * (2 / ρ) ^ k * k.factorial := by ring

end Forward

end

end GroundTheory.Automorphic.Sobolev
