module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrinciple

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem harmonic_eventually_eq_of_ball_le {h : ℂ → ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : InnerProductSpace.HarmonicOnNhd h (Metric.ball z₀ r))
    (hle : ∀ z ∈ Metric.ball z₀ r, h z ≤ h z₀) : ∀ᶠ z in 𝓝 z₀, h z = h z₀ := by
  obtain ⟨F, hF, hre⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hh
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hball : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hnorm : ∀ z ∈ Metric.ball z₀ r, ‖Complex.exp (F z)‖ = Real.exp (h z) := fun z hz => by
    rw [Complex.norm_exp]
    exact congrArg Real.exp (hre hz)
  have hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (F z)) z₀ := by
    filter_upwards [hball] with z hz
    simp only [Function.comp_apply]
    rw [hnorm z hz, hnorm z₀ hz₀]
    exact Real.exp_le_exp.2 (hle z hz)
  filter_upwards [Complex.eventually_eq_of_isLocalMax_norm hdiff hmax, hball] with z hz hzb
  have h1 := congrArg norm hz
  rw [hnorm z hzb, hnorm z₀ hz₀] at h1
  exact Real.exp_injective h1

theorem harmonic_annulus_le_zero : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b →
    ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} →
    (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) →
    (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) →
    ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  intro h a b ha hab hc hh hb z hz1 hz2
  by_contra hpos
  push Not at hpos
  set K : Set ℂ := {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} with hK
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hKcomp : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset hKclosed
      (fun w hw => by simpa using hw.2)
  have hzK : z ∈ K := ⟨hz1, hz2⟩
  obtain ⟨z₁, hz₁K, hz₁⟩ := hKcomp.exists_isMaxOn ⟨z, hzK⟩ hc
  set S : Set ℂ := K ∩ h ⁻¹' {h z₁} with hS
  have hSclosed : IsClosed S :=
    hc.preimage_isClosed_of_isClosed hKclosed isClosed_singleton
  have hScomp : IsCompact S := hKcomp.of_isClosed_subset hSclosed Set.inter_subset_left
  obtain ⟨z₀, hz₀S, hz₀⟩ :=
    hScomp.exists_isMaxOn ⟨z₁, hz₁K, rfl⟩ (continuous_norm.continuousOn (s := S))
  have hz₀K : z₀ ∈ K := hz₀S.1
  have hval : h z₀ = h z₁ := hz₀S.2
  have hMpos : 0 < h z₀ := hval ▸ hpos.trans_le (hz₁ hzK)
  have hlo : a < ‖z₀‖ := lt_of_le_of_ne hz₀K.1 fun e => absurd (hb z₀ (Or.inl e.symm)) (not_le.2 hMpos)
  have hhi : ‖z₀‖ < b := lt_of_le_of_ne hz₀K.2 fun e => absurd (hb z₀ (Or.inr e)) (not_le.2 hMpos)
  have hUopen : IsOpen {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUopen z₀ ⟨hlo, hhi⟩
  have hloc : ∀ᶠ w in 𝓝 z₀, h w = h z₀ := by
    refine harmonic_eventually_eq_of_ball_le hr (fun w hw => hh w (hrU hw).1 (hrU hw).2) ?_
    intro w hw
    rw [hval]
    exact hz₁ ⟨(hrU hw).1.le, (hrU hw).2.le⟩
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1
    (hloc.and (hUopen.mem_nhds ⟨hlo, hhi⟩))
  have hz₀pos : 0 < ‖z₀‖ := ha.trans hlo

  set t : ℝ := ε / (2 * ‖z₀‖) with ht
  have htpos : 0 < t := by positivity
  set w : ℂ := ((1 + t : ℝ) : ℂ) * z₀ with hw
  have hwnorm : ‖w‖ = (1 + t) * ‖z₀‖ := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hdist : dist w z₀ < ε := by
    have e : w - z₀ = (t : ℂ) * z₀ := by
      rw [hw]; push_cast; ring
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le, ht]
    have : ε / (2 * ‖z₀‖) * ‖z₀‖ = ε / 2 := by field_simp
    rw [this]
    linarith
  obtain ⟨hwval, hwU⟩ := hεb w hdist
  have hwS : w ∈ S := ⟨⟨hwU.1.le, hwU.2.le⟩, by simpa [hval] using hwval⟩
  have hle : ‖w‖ ≤ ‖z₀‖ := hz₀ hwS
  rw [hwnorm] at hle
  nlinarith [mul_pos htpos hz₀pos]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrincipleStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

theorem _root_.GlobalTheory.T.harmonic_annulus_maximum_principle : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b → ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} → (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) → (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PoissonIntegralPuncturedDisc

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PuncturedDisc

theorem le_zero_of_bddAbove_punctured (g : ℂ → ℝ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hc : ContinuousOn g {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ})
    (hh : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt g z)
    (h0 : ∀ z : ℂ, ‖z‖ = ρ → g z ≤ 0)
    (hC : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → g z ≤ C) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → g w ≤ 0 := by
  intro w hw0 hwρ
  have hlogw : Real.log ‖w‖ < Real.log ρ := Real.log_lt_log hw0 hwρ
  have hD : 0 < Real.log ρ - Real.log ‖w‖ := sub_pos.mpr hlogw
  have key : ∀ ε : ℝ, 0 < ε → g w ≤ ε * (Real.log ρ - Real.log ‖w‖) := by
    intro ε hε
    have hexp_pos : 0 < Real.exp (-(|C| / ε)) := Real.exp_pos _
    have hexp_le : Real.exp (-(|C| / ε)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ |C| / ε := div_nonneg (abs_nonneg C) hε.le
      linarith
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ‖w‖ * Real.exp (-(|C| / ε)) / 2 := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr_def]
      exact div_pos (mul_pos hw0 hexp_pos) two_pos
    have hrw : r < ‖w‖ := by
      have := mul_le_mul_of_nonneg_left hexp_le hw0.le
      rw [hr_def]
      linarith
    have hrρ : r < ρ := lt_trans hrw hwρ
    have hlogr : Real.log r = Real.log ‖w‖ - |C| / ε - Real.log 2 := by
      rw [hr_def, Real.log_div (mul_pos hw0 hexp_pos).ne' two_ne_zero,
        Real.log_mul hw0.ne' hexp_pos.ne', Real.log_exp]
      ring
    let h : ℂ → ℝ := fun z => g z - ε * (Real.log ρ - Real.log ‖z‖)
    have hcont : ContinuousOn h {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
      have hsub : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} :=
        fun z hz => ⟨lt_of_lt_of_le hr0 hz.1, hz.2⟩
      refine (hc.mono hsub).sub (continuousOn_const.mul (continuousOn_const.sub ?_))
      refine ContinuousOn.log continuous_norm.continuousOn ?_
      intro z hz
      exact (lt_of_lt_of_le hr0 hz.1).ne'
    have hharm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt h z := by
      intro z hz1 hz2
      have hz0 : 0 < ‖z‖ := lt_trans hr0 hz1
      have hlog : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y‖) z :=
        analyticAt_id.harmonicAt_log_norm (norm_pos_iff.mp hz0)
      have hcst : InnerProductSpace.HarmonicAt (fun _ : ℂ => Real.log ρ) z :=
        InnerProductSpace.harmonicAt_const _
      have h2 : InnerProductSpace.HarmonicAt
          (ε • ((fun _ : ℂ => Real.log ρ) - fun y : ℂ => Real.log ‖y‖)) z := by
        apply InnerProductSpace.HarmonicAt.const_smul
        exact hcst.sub hlog
      exact (hh z hz0 hz2).sub h2
    have hbdry : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = ρ → h z ≤ 0 := by
      intro z hz
      rcases hz with hz | hz
      · have hgz : g z ≤ C := hC z (by rw [hz]; exact hr0) (by rw [hz]; exact hrρ.le)
        have hCabs : C ≤ |C| := le_abs_self C
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, hlogr]
        have e1 : ε * (Real.log ρ - (Real.log ‖w‖ - |C| / ε - Real.log 2)) =
            ε * (Real.log ρ - Real.log ‖w‖) + ε * (|C| / ε) + ε * Real.log 2 := by ring
        have e2 : ε * (|C| / ε) = |C| := by field_simp
        rw [e1, e2]
        linarith [mul_pos hε hD, mul_pos hε hlog2]
      · show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, sub_self, mul_zero, sub_zero]
        exact h0 z hz
    have hmax := GlobalTheory.T.harmonic_annulus_maximum_principle h r ρ hr0 hrρ hcont hharm hbdry w hrw.le hwρ.le
    simp only [h] at hmax
    linarith
  by_contra hneg
  have hpos := not_le.mp hneg
  have hk := key (g w / (2 * (Real.log ρ - Real.log ‖w‖))) (div_pos hpos (mul_pos two_pos hD))
  have e3 : g w / (2 * (Real.log ρ - Real.log ‖w‖)) * (Real.log ρ - Real.log ‖w‖) = g w / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hD.ne']
  linarith

theorem poisson_formula_punctured (f : ℂ → ℝ) (ρ R M : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (hH : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → InnerProductSpace.HarmonicAt f z)
    (hB : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → |f z| ≤ M) (w : ℂ) (hw0 : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    ∫ t, pker ρ w t * f (circleMap 0 ρ t) ∂angMeas = f w := by
  have hρabs : |ρ| = ρ := abs_of_pos hρ
  have hfc : ContinuousOn f (Metric.sphere 0 ρ) := by
    intro z hz
    have hz' : ‖z‖ = ρ := by simpa using hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz'
      linarith
    exact (hH z hz0 (by rw [hz']; exact hρR)).1.continuousAt.continuousWithinAt
  have hPbd : ∀ z : ℂ, ‖z‖ < ρ → |ReciprocityTheory.AnForm.A.poissonInt f ρ z| ≤ M := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hup := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb M
    have hlo := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb (-M)
    have hsph : ∀ x ∈ Metric.sphere (0 : ℂ) |ρ|, |f x| ≤ M ∧ 0 ≤ poissonKernel 0 z x := by
      intro x hx
      rw [hρabs] at hx
      have hx' : ‖x‖ = ρ := by simpa using hx
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx'
        linarith
      exact ⟨hB x hx0 (by rw [hx']; exact hρR), ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg hzb hx⟩
    have h1 : 0 ≤ Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).2
        have : 0 ≤ poissonKernel 0 z x * (M - f x) := mul_nonneg hk (by linarith)
        linarith
    have h1' : Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ =
        -Real.circleAverage (fun x => poissonKernel 0 z x * (f x - M)) 0 ρ := by
      simp only [Real.circleAverage, intervalIntegral.integral_neg, smul_neg]
    have h2 : 0 ≤ Real.circleAverage (fun x => poissonKernel 0 z x * (f x - -M)) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).1
        exact mul_nonneg hk (by linarith)
    rw [abs_le]
    constructor <;> linarith
  let Φ : ℂ → ℝ := fun z => if ‖z‖ < ρ then ReciprocityTheory.AnForm.A.poissonInt f ρ z else f z
  have hPharm : ∀ z : ℂ, ‖z‖ < ρ → InnerProductSpace.HarmonicAt Φ z := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hev : Φ =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.poissonInt f ρ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy
      have : ‖y‖ < ρ := by simpa using hy
      simp only [Φ, if_pos this]
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr
      (ReciprocityTheory.AnForm.A.poissonInt_harmonicAt hρ hfc hzb)
  have hΦcont : ContinuousOn Φ (Metric.closedBall 0 ρ) := by
    intro z hz
    by_cases hzl : ‖z‖ < ρ
    · exact (hPharm z hzl).1.continuousAt.continuousWithinAt
    · have hzle : ‖z‖ ≤ ρ := by simpa using hz
      have hzeq : ‖z‖ = ρ := le_antisymm hzle (not_lt.mp hzl)
      have hzs : z ∈ Metric.sphere (0 : ℂ) ρ := by simpa using hzeq
      have hΦz : Φ z = f z := by simp only [Φ, if_neg hzl]
      rw [← Metric.ball_union_sphere]
      apply ContinuousWithinAt.union
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (ReciprocityTheory.AnForm.A.poissonInt_tendsto hρ hfc hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have : ‖y‖ < ρ := by simpa using hy
        simp only [Φ, if_pos this]
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (hfc z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : ‖y‖ = ρ := by simpa using hy
        simp only [Φ, if_neg (not_lt.mpr hy'.ge)]
  have hΦb : ∀ z : ℂ, ‖z‖ = ρ → Φ z = f z := by
    intro z hz
    simp only [Φ, if_neg (not_lt.mpr hz.ge)]
  have hS : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ Metric.closedBall 0 ρ := fun z hz => by
    simpa using hz.2
  have hfS : ContinuousOn f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} := fun z hz =>
    (hH z (norm_pos_iff.mp hz.1) (lt_of_le_of_lt hz.2 hρR)).1.continuousAt.continuousWithinAt
  have hΦbd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → |Φ z| ≤ M := by
    intro z hz0 hzρ
    by_cases hzl : ‖z‖ < ρ
    · simp only [Φ, if_pos hzl]
      exact hPbd z hzl
    · simp only [Φ, if_neg hzl]
      exact hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR)
  have hA := le_zero_of_bddAbove_punctured (fun z => f z - Φ z) ρ (2 * M) hρ
    (hfS.sub (hΦcont.mono hS))
    (fun z hz0 hzρ => (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)).sub (hPharm z hzρ))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hA' := le_zero_of_bddAbove_punctured (fun z => Φ z - f z) ρ (2 * M) hρ
    ((hΦcont.mono hS).sub hfS)
    (fun z hz0 hzρ => (hPharm z hzρ).sub (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hΦw : Φ w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by simp only [Φ, if_pos hwρ]
  have hfw : f w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by linarith
  rw [hfw]
  have hint := GlobalTheory.CompanionTheory.Ar.PB.Flat.integral_angMeas (fun z => poissonKernel 0 w z * f z) ρ
  exact hint

end GlobalTheory.CompanionTheory.Ar.PuncturedDisc
end
end
