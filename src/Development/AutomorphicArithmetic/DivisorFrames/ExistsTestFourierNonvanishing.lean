module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
public import Development.AutomorphicArithmetic.DivisorFrames.GaussianFourierConjPower

@[expose] public section

open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private lemma rad_int (p : ℝ) (hp : -2 < p) :
    Integrable (fun s : ℂ => ‖s‖ ^ p * Real.exp (-Real.pi * ‖s‖ ^ 2)) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ)
    (f := fun r : ℝ => r ^ p * Real.exp (-Real.pi * r ^ 2))]
  have h := integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := p + 1) (by linarith)
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr' : (0 : ℝ) < r := hr
  simp only [Complex.finrank_real_complex, smul_eq_mul]
  rw [Real.rpow_add_one hr'.ne']
  norm_num
  ring

private lemma nat_int (m : ℕ) :
    Integrable (fun s : ℂ => ‖s‖ ^ m * Real.exp (-Real.pi * ‖s‖ ^ 2)) := by
  have := rad_int (m : ℝ) (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  simpa only [Real.rpow_natCast] using this

private noncomputable def gk (k : ℕ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ s) ^ k * Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2)

private lemma cexp_eq (s : ℂ) : Complex.exp (-(Real.pi : ℂ) * (‖s‖ : ℂ) ^ 2)
    = ((Real.exp (-Real.pi * ‖s‖ ^ 2) : ℝ) : ℂ) := by
  push_cast; rfl

private lemma rad_pos (m : ℕ) :
    0 < ∫ s : ℂ, ‖s‖ ^ m * Real.exp (-Real.pi * ‖s‖ ^ 2) := by
  refine integral_pos_of_integrable_nonneg_nonzero (x := 1) (by fun_prop) (nat_int m)
    (fun s => by positivity) ?_
  have := Real.exp_pos (-Real.pi)
  simp

private lemma dual_int (k e : ℕ) (hk : 2 * e < k) :
    Integrable (fun y : ℂ => ((-Complex.I * y) ^ k * Complex.exp (-(Real.pi : ℂ) * (‖y‖ : ℂ) ^ 2)) *
      (((y / (‖y‖ : ℂ)) ^ (k : ℤ) * (‖y‖ : ℂ) ^ (2 * e)) * (‖y‖ : ℂ) ^ 2)⁻¹) := by
  have hp : (-2 : ℝ) < (k : ℝ) - ((2 * e + 2 : ℕ) : ℝ) := by
    have : ((2 * e : ℕ) : ℝ) < k := by exact_mod_cast hk
    push_cast at this ⊢
    linarith
  refine Integrable.mono' (rad_int _ hp) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    have h : Measurable fun s : ℂ => (‖s‖ : ℂ) := Complex.measurable_ofReal.comp measurable_norm
    refine Measurable.mul (by fun_prop) (Measurable.inv ?_)
    exact (((measurable_id.div h).pow_const _).mul (h.pow_const _)).mul (h.pow_const _)
  · have h0 : ∀ᵐ y : ℂ, y ≠ 0 := by
      simp [ae_iff]
    filter_upwards [h0] with y hy
    have h : 0 < ‖y‖ := norm_pos_iff.2 hy
    rw [cexp_eq, Real.rpow_sub h, Real.rpow_natCast, Real.rpow_natCast]
    simp only [norm_mul, norm_inv, norm_pow, norm_zpow, norm_div, Complex.norm_real, norm_norm,
      norm_neg, Complex.norm_I, one_mul, div_self h.ne', one_zpow,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq
    field_simp
    try ring
