module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmA
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InfRight
public import Mathlib.Analysis.Calculus.FDeriv.Mul

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmB

section

@[expose] public section

noncomputable section

open Matrix
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.S7

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

namespace IdB

lemma quad_norm_le (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖star v ⬝ᵥ (H *ᵥ v)‖ ≤ (n : ℝ) * n * (‖v‖ * ‖H‖ * ‖v‖) := by
  have hvi : ∀ i, ‖v i‖ ≤ ‖v‖ := fun i => norm_le_pi_norm v i
  have hH : ∀ i j, ‖H i j‖ ≤ ‖H‖ := fun i j => norm_entry_le_entrywise_sup_norm H
  have key : ∀ i, ‖star (v i) * ∑ j, H i j * v j‖ ≤ ∑ _j : Fin n, ‖v‖ * ‖H‖ * ‖v‖ := by
    intro i
    rw [norm_mul, norm_star]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    have h1 := mul_le_mul (hH i j) (hvi j) (norm_nonneg _) (norm_nonneg _)
    calc ‖v i‖ * (‖H i j‖ * ‖v j‖) ≤ ‖v‖ * (‖H‖ * ‖v‖) :=
          mul_le_mul (hvi i) h1 (by positivity) (norm_nonneg _)
      _ = ‖v‖ * ‖H‖ * ‖v‖ := by ring
  have e : star v ⬝ᵥ (H *ᵥ v) = ∑ i, star (v i) * ∑ j, H i j * v j := by
    simp only [dotProduct, mulVec, Pi.star_apply]
  rw [e]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => key i).trans (le_of_eq ?_))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma quad_scale (x : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (t : ℝ) :
    (star ((t : ℂ) • v) ⬝ᵥ (x *ᵥ ((t : ℂ) • v))).re = t ^ 2 * (star v ⬝ᵥ (x *ᵥ v)).re := by
  rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc]
  have : (t : ℂ) * star (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]; push_cast; ring
  rw [this, Complex.re_ofReal_mul]

lemma quad_lower {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ c > 0, ∀ v : Fin n → ℂ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (x *ᵥ v)).re := by
  have hq : Continuous fun v : Fin n → ℂ => (star v ⬝ᵥ (x *ᵥ v)).re :=
    Complex.continuous_re.comp (continuous_id.star.dotProduct (continuous_const.matrix_mulVec continuous_id))
  have hpos : ∀ v : Fin n → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ (x *ᵥ v)).re := fun v hv => by
    have h := (Complex.lt_def.mp (hx.dotProduct_mulVec_pos hv)).1
    simpa using h
  have hnorm : ∀ v : Fin n → ℂ, v ≠ 0 → ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := fun v hv => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hback : ∀ v : Fin n → ℂ, v ≠ 0 → ((‖v‖ : ℝ) : ℂ) • (((‖v‖⁻¹ : ℝ) : ℂ) • v) = v := fun v hv => by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), Complex.ofReal_one,
      one_smul]
  by_cases hS : ∃ u : Fin n → ℂ, ‖u‖ = 1
  · obtain ⟨u, hu⟩ := hS
    have hne : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty := ⟨u, by simpa using hu⟩
    obtain ⟨u0, hu0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hne hq.continuousOn
    have hu0n : ‖u0‖ = 1 := by simpa using hu0
    have hu00 : u0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu0n
      exact zero_ne_one hu0n
    refine ⟨_, hpos u0 hu00, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · set u := ((‖v‖⁻¹ : ℝ) : ℂ) • v
      have hum : u ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        exact hnorm v hv
      have h1 := hmin hum
      rw [← hback v hv, quad_scale]
      have : ‖((‖v‖ : ℝ) : ℂ) • u‖ = ‖v‖ := by rw [hback v hv]
      rw [this, mul_comm]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
  · refine ⟨1, one_pos, fun v => ?_⟩
    by_cases hv : v = 0
    · subst hv
      simp
    · exact absurd ⟨_, hnorm v hv⟩ hS

theorem posDef_nhd {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    ∃ δ > 0, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ‖H‖ < δ → (x + H).PosDef := by
  obtain ⟨c, hc, hq⟩ := quad_lower hx
  refine ⟨c / ((n : ℝ) * n + 1), by positivity, fun H hH hHn => ?_⟩
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨hx.isHermitian.add hH, fun v hv => ?_⟩
  rw [Complex.lt_def]
  have him := (hx.isHermitian.add hH).im_star_dotProduct_mulVec_self v
  have e : star v ⬝ᵥ ((x + H) *ᵥ v) = star v ⬝ᵥ (x *ᵥ v) + star v ⬝ᵥ (H *ᵥ v) := by
    rw [add_mulVec, dotProduct_add]
  refine ⟨?_, ?_⟩
  · rw [e, Complex.add_re, Complex.zero_re]
    have h1 := hq v
    have h2 := quad_norm_le H v
    have h3 : -‖star v ⬝ᵥ (H *ᵥ v)‖ ≤ (star v ⬝ᵥ (H *ᵥ v)).re := by
      have := Complex.abs_re_le_norm (star v ⬝ᵥ (H *ᵥ v))
      linarith [neg_abs_le (star v ⬝ᵥ (H *ᵥ v)).re]
    have hv2 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.mpr hv; positivity
    have hN : (0 : ℝ) ≤ (n : ℝ) * n := by positivity
    have hHpos : 0 ≤ ‖H‖ := norm_nonneg _
    have hδ : ((n : ℝ) * n + 1) * ‖H‖ < c := by
      rw [lt_div_iff₀ (by positivity)] at hHn
      linarith
    have h4 : 0 < (c - (n : ℝ) * n * ‖H‖) * ‖v‖ ^ 2 := mul_pos (by nlinarith) hv2
    nlinarith
  · rw [Complex.zero_im]
    simpa using him.symm

theorem line_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (g : ℂ → F)
    (hg : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s) (hr : ∀ t : ℝ, |t| < 2 → g t = 0) :
    g Complex.I = 0 := by
  have hDO : DifferentiableOn ℂ g (Metric.ball 0 2) := fun s hs =>
    (hg s (by simpa using hs)).differentiableWithinAt
  have han := hDO.analyticOnNhd Metric.isOpen_ball
  have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
  have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ, g (t : ℂ) = 0 := by
    have h2 : ∀ᶠ t in nhds (0 : ℝ), |t| < 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) two_pos] with t ht
      simpa [Real.dist_eq] using ht
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds h2).mono fun t h => hr t h
  have hfreq : ∃ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, g s = 0 := ht.frequently hev.frequently
  have hz := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball (0 : ℂ) 2).isPreconnected
    (Metric.mem_ball_self two_pos) hfreq
  have hI : Complex.I ∈ Metric.ball (0 : ℂ) 2 := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_I]
    norm_num
  simpa using hz hI

end IdB

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsMInfNhd

section

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {lam : Fin n → ℝ}

theorem psM_inf_nhd (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ Y : Matrix (Fin n) (Fin n) ℂ, IsBlock ε Y →
        fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z) ∧
          fderiv ℂ (psM T μ) z (Y * z) = -(psM T μ z * T.dτ Y) := by
  obtain ⟨U0, hU0o, hpos0, hΩ, hdiff, hfd⟩ := psM_holo (μ := μ) T
  refine ⟨{z | ∃ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef ∧ ∃ r : ℝ, 0 < r ∧ ‖z - x‖ < r ∧
      (∀ w : Matrix (Fin n) (Fin n) ℂ, ‖w - x‖ < 3 * r → w ∈ U0) ∧
      (∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian → ‖H‖ < 3 * r → (x + H).PosDef)},
      ?_, ?_, ?_, ?_⟩
  · refine Metric.isOpen_iff.mpr ?_
    rintro z ⟨x, hx, r, hr, hzx, hU, hP⟩
    refine ⟨r - ‖z - x‖, sub_pos.mpr hzx, fun z' hz' => ⟨x, hx, r, hr, ?_, hU, hP⟩⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz'
    have h1 : z' - x = (z' - z) + (z - x) := by abel
    rw [h1]
    have h2 := norm_add_le (z' - z) (z - x)
    linarith
  · intro x hx
    have hx' : x.PosDef := hx
    obtain ⟨δ, hδ, hδP⟩ := IdB.posDef_nhd hx'
    obtain ⟨e, he, heU⟩ := Metric.isOpen_iff.mp hU0o x (hpos0 hx)
    have hm : 0 < min δ e / 3 := div_pos (lt_min hδ he) (by norm_num)
    refine ⟨x, hx', min δ e / 3, hm, by rw [sub_self, norm_zero]; exact hm, ?_, ?_⟩
    · intro w hw
      apply heU
      rw [Metric.mem_ball, dist_eq_norm]
      have : min δ e ≤ e := min_le_right δ e
      linarith
    · intro H hH hHn
      apply hδP H hH
      have : min δ e ≤ δ := min_le_left δ e
      linarith
  · refine hdiff.mono ?_
    intro z hz
    obtain ⟨x, hx, r, hr, hzx, hU, hP⟩ := hz
    exact hU z (by linarith)
  · rintro z ⟨x, hx, r, hr, hzx, hU, hP⟩ Y hY
    have hxH : xᴴ = x := hx.1.eq
    have h12 : star (1 / 2 : ℂ) = 1 / 2 := by
      have h := Complex.conj_ofReal (1 / 2 : ℝ)
      push_cast at h
      exact h
    have hsI : star Complex.I = -Complex.I := Complex.conj_I
    have hn12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℂ, A = (1 / 2 : ℂ) • (z + zᴴ) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) ℂ,
        B = (1 / 2 : ℂ) • (Complex.I • (zᴴ - z)) := ⟨_, rfl⟩
    have hAH : A.IsHermitian := by
      rw [Matrix.IsHermitian, hA]
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
        star_mul', star_add, star_star, h12]
      ring
    have hBH : B.IsHermitian := by
      rw [Matrix.IsHermitian, hB]
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        star_mul', star_sub, star_star, h12, hsI]
      ring
    have hAB : A + Complex.I • B = z := by
      rw [hA, hB]
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
        smul_eq_mul]
      linear_combination ((1 / 2 : ℂ) * (star (z j i) - z i j)) * Complex.I_sq
    have hAx : A - x = (1 / 2 : ℂ) • ((z - x) + (z - x)ᴴ) := by
      rw [hA, Matrix.conjTranspose_sub, hxH]; module
    have hBx : B = (1 / 2 : ℂ) • (Complex.I • ((z - x)ᴴ - (z - x))) := by
      rw [hB, Matrix.conjTranspose_sub, hxH]; module
    have hAn : ‖A - x‖ ≤ ‖z - x‖ := by
      have h := norm_add_le (z - x) (z - x)ᴴ
      rw [Matrix.norm_conjTranspose] at h
      rw [hAx, norm_smul, hn12]
      linarith
    have hBn : ‖B‖ ≤ ‖z - x‖ := by
      have h := norm_sub_le (z - x)ᴴ (z - x)
      rw [Matrix.norm_conjTranspose] at h
      rw [hBx, norm_smul, norm_smul, hn12, Complex.norm_I]
      linarith
    have hbound : ∀ s : ℂ, ‖s‖ < 2 → ‖A + s • B - x‖ < 3 * r := by
      intro s hs
      have e1 : A + s • B - x = (A - x) + s • B := by abel
      rw [e1]
      have h1 := norm_add_le (A - x) (s • B)
      rw [norm_smul] at h1
      have h2 : ‖s‖ * ‖B‖ ≤ 2 * ‖z - x‖ := mul_le_mul hs.le hBn (norm_nonneg _) (by norm_num)
      linarith
    have key : ∀ s : ℂ, ‖s‖ < 2 → A + s • B ∈ U0 := fun s hs => hU _ (hbound s hs)
    have hposR : ∀ t : ℝ, |t| < 2 → (A + (t : ℂ) • B).PosDef := by
      intro t ht
      have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
      have hBt : ((t : ℂ) • B).IsHermitian := by
        rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hBH.eq]
        rw [show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t]
      have hH : (A + (t : ℂ) • B - x).IsHermitian := (hAH.add hBt).sub hx.1
      have := hP _ hH (hbound _ hs)
      simpa using this
    have hI : ‖Complex.I‖ < 2 := by rw [Complex.norm_I]; norm_num
    constructor
    · let g : ℂ → (T.V →L[ℂ] T.V) := fun s =>
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k,
            toMK k⁻¹ * (A * Y + s • (B * Y)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
          + T.dτ Y * psM T μ (A + s • B)
      have hgeq : ∀ s : ℂ, A + s • B ∈ U0 →
          g s = fderiv ℂ (psM T μ) (A + s • B) ((A + s • B) * Y) + T.dτ Y * psM T μ (A + s • B) := by
        intro s hs
        rw [hfd _ hs]
        simp only [g, add_mul, Matrix.smul_mul] <;> rfl
      have hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s := by
        intro s hs
        have hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s :=
          (differentiableAt_const A).add (differentiableAt_id.smul_const B)
        have hψ := (hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw
        exact ((line_int_differentiableAt T μ hU0o hΩ A B (A * Y) (B * Y) (key s hs)).const_smul
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.const_mul (T.dτ Y))
      have hgr : ∀ t : ℝ, |t| < 2 → g t = 0 := by
        intro t ht
        have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
        rw [hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).1]
        simp
      have h0 := IdB.line_zero g hgd hgr
      rw [hgeq _ (key _ hI), hAB] at h0
      exact eq_neg_of_add_eq_zero_left h0
    · let g : ℂ → (T.V →L[ℂ] T.V) := fun s =>
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          (∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (A + s • B) * toMK k,
            toMK k⁻¹ * (Y * A + s • (Y * B)) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))
          + psM T μ (A + s • B) * T.dτ Y
      have hgeq : ∀ s : ℂ, A + s • B ∈ U0 →
          g s = fderiv ℂ (psM T μ) (A + s • B) (Y * (A + s • B)) + psM T μ (A + s • B) * T.dτ Y := by
        intro s hs
        rw [hfd _ hs]
        simp only [g, mul_add, Matrix.mul_smul] <;> rfl
      have hgd : ∀ s : ℂ, ‖s‖ < 2 → DifferentiableAt ℂ g s := by
        intro s hs
        have hw : DifferentiableAt ℂ (fun y : ℂ => A + y • B) s :=
          (differentiableAt_const A).add (differentiableAt_id.smul_const B)
        have hψ := (hdiff.differentiableAt (hU0o.mem_nhds (key s hs))).comp s hw
        exact ((line_int_differentiableAt T μ hU0o hΩ A B (Y * A) (Y * B) (key s hs)).const_smul
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ))).add (hψ.mul_const (T.dτ Y))
      have hgr : ∀ t : ℝ, |t| < 2 → g t = 0 := by
        intro t ht
        have hs : ‖(t : ℂ)‖ < 2 := by rwa [Complex.norm_real, Real.norm_eq_abs]
        rw [hgeq _ (key _ hs), (psM_inf_right T μ hμ (hposR t ht) hY).2]
        simp
      have h0 := IdB.line_zero g hgd hgr
      rw [hgeq _ (key _ hI), hAB] at h0
      exact eq_neg_of_add_eq_zero_left h0

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
end
