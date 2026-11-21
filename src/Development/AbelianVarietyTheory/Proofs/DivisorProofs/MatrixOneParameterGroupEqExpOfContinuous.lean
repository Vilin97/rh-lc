module

public import Mathlib

@[expose] public section

open Filter MeasureTheory Topology

namespace GlobalTheory.OneParamMatrix

open scoped Matrix.Norms.Operator

theorem eq_exp_of_continuous_oneParameter {n : Type} [Fintype n] [DecidableEq n]
    (N : ℝ → Matrix n n ℂ) (hc : Continuous N) (h0 : N 0 = 1)
    (hm : ∀ s t, N (s + t) = N s * N t) :
    ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  have hd : DifferentiableAt ℝ N 0 := by
    let G (x : ℝ) := ∫ s in (0 : ℝ)..x, N s
    have hG (x : ℝ) : HasDerivAt G (N x) x :=
      (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
    have hlim : Tendsto (fun δ : ℝ => δ⁻¹ • G δ) (𝓝[≠] 0) (𝓝 1) := by
      have hG0 : G 0 = 0 := intervalIntegral.integral_same
      have h := hasDerivAt_iff_tendsto_slope_zero.mp (hG 0)
      rw [h0] at h
      refine h.congr' (Eventually.of_forall fun δ => ?_)
      simp only [zero_add, hG0, sub_zero]
    obtain ⟨δ, havg, hδ⟩ :=
      ((hlim.eventually (Units.isOpen.mem_nhds isUnit_one)).and self_mem_nhdsWithin).exists
    have hδ₀ : δ ≠ 0 := hδ
    have hunit : IsUnit (G δ) := by
      have hscale : algebraMap ℝ (Matrix n n ℂ) δ * (δ⁻¹ • G δ) = G δ := by
        rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ₀, one_smul]
      rw [← hscale]
      exact ((Ne.isUnit hδ₀).map _).mul havg
    have htranslate (t : ℝ) : N t * G δ = G (t + δ) - G t := by
      have hmul := (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) (N t)).intervalIntegral_comp_comm
        (hc.intervalIntegrable (μ := volume) 0 δ)
      simp only [ContinuousLinearMap.mul_apply'] at hmul
      dsimp only [G]
      rw [← hmul, intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
      simp_rw [← hm]
      rw [intervalIntegral.integral_comp_add_left (fun s => N s) t, add_zero]
    have hshift : DifferentiableAt ℝ (fun t => G (t + δ)) 0 :=
      (hG (0 + δ)).differentiableAt.comp 0 (differentiableAt_id.add_const δ)
    have hform : N = fun t => (G (t + δ) - G t) * (↑(hunit.unit⁻¹) : Matrix n n ℂ) := by
      funext t
      rw [← htranslate, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [hform]
    exact (hshift.sub (hG 0).differentiableAt).mul_const _
  set Y := deriv N 0 with hY
  have hN : ∀ t, HasDerivAt N (N t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => N t * N (s - t)) (N t * Y) t := by
      have h2 : HasDerivAt (fun s => N (s - t)) Y t := by
        have hd' : HasDerivAt N Y (t - t) := by rw [sub_self]; exact hd.hasDerivAt
        exact hd'.comp_sub_const t t
      exact h2.const_mul (N t)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only
    rw [← hm]; congr 1; ring
  refine ⟨Y, fun t => ?_⟩
  set f : ℝ → Matrix n n ℂ := fun s => N s * NormedSpace.exp ((-s) • Y) with hf
  have hfd : ∀ s, HasDerivAt f 0 s := by
    intro s
    have he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Y))) (NormedSpace.exp (s • (-Y)) * (-Y)) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) s
    have he' : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • Y))
        (NormedSpace.exp ((-s) • Y) * (-Y)) s := by
      simpa [smul_neg, neg_smul] using he
    have := (hN s).mul he'
    refine this.congr_deriv ?_
    have hcomm : Y * NormedSpace.exp ((-s) • Y) = NormedSpace.exp ((-s) • Y) * Y :=
      ((Commute.refl Y).smul_right (-s)).exp_right.eq
    rw [mul_assoc, hcomm]
    simp [mul_neg]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hfd s).differentiableAt)
    (fun s => (hfd s).deriv) t 0
  have hf0 : f 0 = 1 := by simp [hf, h0]
  rw [hf0] at hconst
  have hinv : NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
    simp
  calc N t = N t * (NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y)) := by rw [hinv, mul_one]
    _ = f t * NormedSpace.exp (t • Y) := by simp only [hf, mul_assoc]
    _ = NormedSpace.exp (t • Y) := by rw [hconst, one_mul]

end GlobalTheory.OneParamMatrix
