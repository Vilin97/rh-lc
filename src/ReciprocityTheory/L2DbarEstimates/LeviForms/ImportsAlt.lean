module

public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
public import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

-- Source module: ReciprocityTheory.L2DbarEstimates.LeviForms.Bergman

section

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff NNReal

noncomputable section

section
variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M]

def bgDens (ps : M → ℝ) (x : M) : ℝ≥0 := Real.toNNReal (Real.exp (-ps x))

def bgMeas (n : ℕ) (z : M → V n) (ps : M → ℝ) : Measure M :=
  (vol n z).withDensity (fun x => (bgDens ps x : ℝ≥0∞))

theorem bg_wint_eq_lintegral (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ) :
    wint n z f ps = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂bgMeas n z ps := by
  have hm : Measurable (fun x => (bgDens ps x : ℝ≥0∞)) :=
    ((Real.measurable_exp.comp hps.neg).real_toNNReal).coe_nnreal_ennreal
  unfold bgMeas wint
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hm
    (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, bgDens]
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two, mul_comm (‖f x‖ ^ 2), ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

theorem bg_eLpNorm_two_eq (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ) :
    eLpNorm' f 2 (bgMeas n z ps) = wint n z f ps ^ (1/(2:ℝ)) := by
  rw [eLpNorm'_eq_lintegral_eNorm, bg_wint_eq_lintegral n z ps hps f]

theorem bg_memLp_of_wint (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ)
    (hf : AEStronglyMeasurable f (bgMeas n z ps)) (h : wint n z f ps < ⊤) :
    MemLp f 2 (bgMeas n z ps) := by
  change eLpNorm f 2 (bgMeas n z ps) < ⊤
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf, ENNReal.toReal_ofNat, bg_eLpNorm_two_eq n z ps hps f]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne

theorem bg_wint_lt_top_of_memLp (n : ℕ) (z : M → V n) (ps : M → ℝ) (hps : Measurable ps) (f : M → ℂ)
    (hf : MemLp f 2 (bgMeas n z ps)) : wint n z f ps < ⊤ := by
  have h : eLpNorm f 2 (bgMeas n z ps) < ⊤ := hf
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hf.aestronglyMeasurable, ENNReal.toReal_ofNat, bg_eLpNorm_two_eq n z ps hps f] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h

end

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]

def bgHoloSub (n : ℕ) (z : M → V n) (ps : M → ℝ) : Submodule ℂ (Lp ℂ 2 (bgMeas n z ps)) where
  carrier := {f | ∃ G, Holo n z G ∧ (f : M → ℂ) =ᵐ[bgMeas n z ps] G}
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    refine ⟨F + G, fun e he => (hF e he).add (hG e he), ?_⟩
    filter_upwards [Lp.coeFn_add f g, hf, hg] with x h1 h2 h3
    rw [h1, Pi.add_apply, Pi.add_apply, h2, h3]
  zero_mem' := ⟨0, fun e _ => differentiableOn_const (0 : ℂ), Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c f ⟨F, hF, hf⟩
    refine ⟨c • F, fun e he => (hF e he).const_smul c, ?_⟩
    filter_upwards [Lp.coeFn_smul c f, hf] with x h1 h2
    rw [h1, Pi.smul_apply, Pi.smul_apply, h2]

theorem bgHoloSub_closed (n : ℕ) (X : EtaleStein n M) (ps : M → ℝ) (hps : SmoothR n X.z ps)
    (hpsm : Measurable ps) (hC : HoloClosedNeed n M) :
    IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps))) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hFS, hF⟩ := mem_closure_iff_seq_limit.1 hf
  have hFS' : ∀ k, ∃ G, Holo n X.z G ∧ (F k : M → ℂ) =ᵐ[bgMeas n X.z ps] G := fun k => hFS k
  choose G hG hGe using hFS'
  have hfa := Lp.aestronglyMeasurable f
  have hf0m : Measurable (hfa.mk (f : M → ℂ)) := hfa.stronglyMeasurable_mk.measurable
  have hf0 : (f : M → ℂ) =ᵐ[bgMeas n X.z ps] hfa.mk (f : M → ℂ) := hfa.ae_eq_mk
  have hw : ∀ k, wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps =
      (eLpNorm (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps)) ^ (2 : ℝ) := by
    intro k
    have h1 := bg_eLpNorm_two_eq n X.z ps hpsm (fun x => G k x - hfa.mk (f : M → ℂ) x)
    have h2 : eLpNorm' (fun x => G k x - hfa.mk (f : M → ℂ) x) 2 (bgMeas n X.z ps) =
        eLpNorm' (⇑(F k) - ⇑f) 2 (bgMeas n X.z ps) := by
      apply eLpNorm'_congr_ae
      filter_upwards [hGe k, hf0] with x h3 h4
      rw [Pi.sub_apply, h3, h4]
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)
      ((Lp.aestronglyMeasurable (F k)).sub (Lp.aestronglyMeasurable f)), ENNReal.toReal_ofNat, ← h2, h1, ← ENNReal.rpow_mul]
    norm_num
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F f).1 hF
  have hw0 : Tendsto (fun k => wint n X.z (fun x => G k x - hfa.mk (f : M → ℂ) x) ps) atTop (𝓝 0) := by
    simp_rw [hw]
    have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp ht
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at this
    exact this
  obtain ⟨G0, hG0, hfe⟩ := hC X ps G (hfa.mk (f : M → ℂ)) hps hG hf0m hw0
  show ∃ G, Holo n X.z G ∧ (f : M → ℂ) =ᵐ[bgMeas n X.z ps] G
  refine ⟨G0, hG0, hf0.trans ?_⟩
  exact (withDensity_absolutelyContinuous (vol n X.z) _ : bgMeas n X.z ps ≪ vol n X.z).ae_eq hfe

theorem bergmanExists (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : HoloClosedNeed n M) : BergmanExistsStatement n M := by
  intro X ps F0 hps hF0 hw
  have hpsc : Continuous ps := by
    have := Smooth.continuous n X.z X.isLocalHomeomorph _ hps
    exact (Complex.continuous_re.comp this).congr fun x => by simp
  have hpsm : Measurable ps := hpsc.measurable
  have hF0L : MemLp F0 2 (bgMeas n X.z ps) :=
    bg_memLp_of_wint n X.z ps hpsm F0 hF0.aestronglyMeasurable hw
  have hK : IsClosed (bgHoloSub n X.z ps : Set (Lp ℂ 2 (bgMeas n X.z ps))) :=
    bgHoloSub_closed n X ps hps hpsm hC
  haveI : CompleteSpace (bgHoloSub n X.z ps) := hK.completeSpace_coe
  set K := bgHoloSub n X.z ps with hKdef
  set P : Lp ℂ 2 (bgMeas n X.z ps) := (K.orthogonalProjection (hF0L.toLp F0) : Lp ℂ 2 (bgMeas n X.z ps))
    with hPdef
  have hPK : ∃ G, Holo n X.z G ∧ (P : M → ℂ) =ᵐ[bgMeas n X.z ps] G :=
    (K.orthogonalProjection (hF0L.toLp F0)).2
  obtain ⟨G, hG, hPG⟩ := hPK
  refine ⟨G, hG, bg_wint_lt_top_of_memLp n X.z ps hpsm G (MemLp.ae_eq hPG (Lp.memLp P)), ?_⟩
  intro H hH hwH
  have hHc : Continuous H := Smooth.continuous n X.z X.isLocalHomeomorph H (Holo.smooth n X.z H hH)
  have hHL : MemLp H 2 (bgMeas n X.z ps) :=
    bg_memLp_of_wint n X.z ps hpsm H hHc.aestronglyMeasurable hwH
  have hHK : hHL.toLp H ∈ K := show ∃ G, Holo n X.z G ∧ _ from ⟨H, hH, hHL.coeFn_toLp⟩
  have horth : inner ℂ (hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) (hF0L.toLp F0 - P) = 0 := by
    first
    | exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_starProjection_mem_orthogonal _)
    | exact Submodule.inner_right_of_mem_orthogonal hHK (K.sub_orthogonalProjection_mem_orthogonal _)
    | exact Submodule.inner_right_of_mem_orthogonal hHK (sub_orthogonalProjection_mem_orthogonal _)
    | exact orthogonalProjection_inner_eq_zero _ _ hHK
  rw [MeasureTheory.L2.inner_def] at horth
  have hint : ∫ a, inner ℂ ((hHL.toLp H : Lp ℂ 2 (bgMeas n X.z ps)) a)
      ((hF0L.toLp F0 - P : Lp ℂ 2 (bgMeas n X.z ps)) a) ∂(bgMeas n X.z ps) =
      ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps) := by
    refine integral_congr_ae ?_
    filter_upwards [hHL.coeFn_toLp, hF0L.coeFn_toLp, Lp.coeFn_sub (hF0L.toLp F0) P, hPG] with a h1 h2 h3 h4
    rw [h3, Pi.sub_apply, h1, h2, h4]
    simp [RCLike.inner_apply]
    try ring
  have hdm : Measurable (bgDens ps) := (Real.measurable_exp.comp hpsm.neg).real_toNNReal
  have key : ∫ x, (F0 x - G x) * (starRingEnd ℂ) (H x) * (Real.exp (-ps x) : ℂ) ∂vol n X.z =
      ∫ a, (starRingEnd ℂ) (H a) * (F0 a - G a) ∂(bgMeas n X.z ps) := by
    rw [bgMeas, integral_withDensity_eq_integral_smul hdm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [bgDens, NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le, Complex.real_smul]
    ring
  rw [key, ← hint]
  exact horth

end

end ReciprocityTheory.L2DbarEstimates.I
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.LeviForms.TwBound

section

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem twb_pyth {α : Type*} [MeasurableSpace α] (μ : Measure α) (w G : α → ℂ) (ρ : α → ℝ)
    (hw : Measurable w) (hG : Measurable G) (hρm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x)
    (hwf : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 * ρ x) ∂μ < ⊤)
    (hGf : ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2 * ρ x) ∂μ < ⊤)
    (horth : ∫ x, w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ) ∂μ = 0) :
    ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2 * ρ x) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (‖w x - G x‖ ^ 2 * ρ x) ∂μ := by
  have hA0 : ∀ x, 0 ≤ ‖w x‖ ^ 2 * ρ x := fun x => mul_nonneg (sq_nonneg _) (hρ x)
  have hB0 : ∀ x, 0 ≤ ‖G x‖ ^ 2 * ρ x := fun x => mul_nonneg (sq_nonneg _) (hρ x)
  have hC0 : ∀ x, 0 ≤ ‖w x - G x‖ ^ 2 * ρ x := fun x => mul_nonneg (sq_nonneg _) (hρ x)
  have hAm : Measurable (fun x => ‖w x‖ ^ 2 * ρ x) := (hw.norm.pow_const 2).mul hρm
  have hBm : Measurable (fun x => ‖G x‖ ^ 2 * ρ x) := (hG.norm.pow_const 2).mul hρm
  have hAi : Integrable (fun x => ‖w x‖ ^ 2 * ρ x) μ :=
    ⟨hAm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hA0)).2 hwf⟩
  have hBi : Integrable (fun x => ‖G x‖ ^ 2 * ρ x) μ :=
    ⟨hBm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hB0)).2 hGf⟩
  have hPm : Measurable (fun x => w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ)) :=
    (hw.mul (Complex.continuous_conj.measurable.comp hG)).mul
      (Complex.measurable_ofReal.comp hρm)
  have hPi : Integrable (fun x => w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ)) μ := by
    refine (hAi.add hBi).mono' hPm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hρ x)]
    nlinarith [mul_nonneg (sq_nonneg (‖w x‖ - ‖G x‖)) (hρ x),
      mul_nonneg (mul_nonneg (norm_nonneg (w x)) (norm_nonneg (G x))) (hρ x)]
  have hPre := Complex.reCLM.integrable_comp hPi
  simp only [Complex.reCLM_apply] at hPre
  have hre : ∀ x, ‖w x - G x‖ ^ 2 * ρ x = ‖w x‖ ^ 2 * ρ x + ‖G x‖ ^ 2 * ρ x
      - 2 * (w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ)).re := by
    intro x
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im]
    ring
  have hCi : Integrable (fun x => ‖w x - G x‖ ^ 2 * ρ x) μ := by
    refine ((hAi.add hBi).sub (hPre.const_mul 2)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [hre x]
  have hP0 : ∫ x, (w x * (starRingEnd ℂ) (G x) * (ρ x : ℂ)).re ∂μ = 0 := by
    have h1 := Complex.reCLM.integral_comp_comm hPi
    simp only [Complex.reCLM_apply] at h1
    rw [h1, horth, Complex.zero_re]
  have hint : ∫ x, ‖w x - G x‖ ^ 2 * ρ x ∂μ = ∫ x, ‖w x‖ ^ 2 * ρ x ∂μ + ∫ x, ‖G x‖ ^ 2 * ρ x ∂μ := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hre)]
    rw [integral_sub, integral_add, integral_const_mul, hP0, mul_zero, sub_zero]
    all_goals first | exact hAi | exact hBi | exact hAi.add hBi | exact hPre.const_mul 2
  rw [← ofReal_integral_eq_lintegral_ofReal hAi (Filter.Eventually.of_forall hA0),
    ← ofReal_integral_eq_lintegral_ofReal hCi (Filter.Eventually.of_forall hC0)]
  apply ENNReal.ofReal_le_ofReal
  rw [hint]
  linarith [integral_nonneg (μ := μ) (f := fun x => ‖G x‖ ^ 2 * ρ x) (fun x => hB0 x)]

theorem twb_sub_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℂ) (ρ : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hρm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x) :
    ∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ 2 * ρ x) ∂μ ≤
      2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) ∂μ +
        2 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * ρ x) ∂μ := by
  have hm1 : Measurable (fun x => ENNReal.ofReal (‖f x‖ ^ 2 * ρ x)) :=
    ((hf.norm.pow_const 2).mul hρm).ennreal_ofReal
  have hm2 : Measurable (fun x => ENNReal.ofReal (‖g x‖ ^ 2 * ρ x)) :=
    ((hg.norm.pow_const 2).mul hρm).ennreal_ofReal
  calc ∫⁻ x, ENNReal.ofReal (‖f x - g x‖ ^ 2 * ρ x) ∂μ
      ≤ ∫⁻ x, (2 * ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) + 2 * ENNReal.ofReal (‖g x‖ ^ 2 * ρ x)) ∂μ := by
        refine lintegral_mono (fun x => ?_)
        have ha : 0 ≤ ‖f x‖ ^ 2 * ρ x := mul_nonneg (sq_nonneg _) (hρ x)
        have hb : 0 ≤ ‖g x‖ ^ 2 * ρ x := mul_nonneg (sq_nonneg _) (hρ x)
        have h1 : ‖f x - g x‖ ≤ ‖f x‖ + ‖g x‖ := norm_sub_le _ _
        have h3 : ‖f x - g x‖ ^ 2 ≤ (‖f x‖ + ‖g x‖) ^ 2 := by gcongr
        have h2 : ‖f x - g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
          nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)]
        have key : ‖f x - g x‖ ^ 2 * ρ x ≤ 2 * (‖f x‖ ^ 2 * ρ x) + 2 * (‖g x‖ ^ 2 * ρ x) := by
          have h4 := mul_le_mul_of_nonneg_right h2 (hρ x)
          linarith
        calc ENNReal.ofReal (‖f x - g x‖ ^ 2 * ρ x)
            ≤ ENNReal.ofReal (2 * (‖f x‖ ^ 2 * ρ x) + 2 * (‖g x‖ ^ 2 * ρ x)) :=
              ENNReal.ofReal_le_ofReal key
          _ = 2 * ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) + 2 * ENNReal.ofReal (‖g x‖ ^ 2 * ρ x) := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
              simp
    _ = 2 * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2 * ρ x) ∂μ +
          2 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2 * ρ x) ∂μ := by
        rw [lintegral_add_left (hm1.const_mul 2), lintegral_const_mul 2 hm1,
          lintegral_const_mul 2 hm2]

theorem twb_wmono {α : Type*} [MeasurableSpace α] (μ : Measure α) (f ρ₁ ρ₂ : α → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hf : ∀ x, 0 ≤ f x) (h : ∀ x, ρ₁ x ≤ c * ρ₂ x) :
    ∫⁻ x, ENNReal.ofReal (f x * ρ₁ x) ∂μ ≤ ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x * ρ₂ x) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono (fun x => ?_)
  rw [← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  calc f x * ρ₁ x ≤ f x * (c * ρ₂ x) := mul_le_mul_of_nonneg_left (h x) (hf x)
    _ = c * (f x * ρ₂ x) := by ring

theorem twb_pt (p a b T : ℝ) (D0 DP u : ℂ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (h0 : ‖D0‖ ^ 2 ≤ a * T) (h1 : ‖DP‖ ^ 2 ≤ b * T) :
    ‖Complex.exp p * (D0 + u * DP)‖ ^ 2 ≤
      Real.exp (2 * p) * (Real.sqrt a + ‖u‖ * Real.sqrt b) ^ 2 * T := by
  have hD0 : ‖D0‖ ≤ Real.sqrt a * Real.sqrt T := by
    rw [← Real.sqrt_mul ha]
    have h2 := Real.abs_le_sqrt h0
    rwa [abs_of_nonneg (norm_nonneg _)] at h2
  have hDP : ‖DP‖ ≤ Real.sqrt b * Real.sqrt T := by
    rw [← Real.sqrt_mul hb]
    have h2 := Real.abs_le_sqrt h1
    rwa [abs_of_nonneg (norm_nonneg _)] at h2
  have hsum : ‖D0 + u * DP‖ ≤ (Real.sqrt a + ‖u‖ * Real.sqrt b) * Real.sqrt T := by
    calc ‖D0 + u * DP‖ ≤ ‖D0‖ + ‖u‖ * ‖DP‖ := by rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ Real.sqrt a * Real.sqrt T + ‖u‖ * (Real.sqrt b * Real.sqrt T) := by gcongr
      _ = (Real.sqrt a + ‖u‖ * Real.sqrt b) * Real.sqrt T := by ring
  have hT' : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT
  have he : Real.exp p ^ 2 = Real.exp (2 * p) := by rw [sq, ← Real.exp_add, two_mul]
  rw [norm_mul, Complex.norm_exp_ofReal, mul_pow]
  calc Real.exp p ^ 2 * ‖D0 + u * DP‖ ^ 2
      ≤ Real.exp p ^ 2 * ((Real.sqrt a + ‖u‖ * Real.sqrt b) * Real.sqrt T) ^ 2 := by gcongr
    _ = Real.exp (2 * p) * (Real.sqrt a + ‖u‖ * Real.sqrt b) ^ 2 * T := by
        rw [mul_pow, hT', he]; ring

theorem twb_dbar {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (F0 F : M → ℂ)
    (Ph : M → ℝ) (hF0 : Smooth n z F0) (hF : Holo n z F) (hPh : SmoothR n z Ph) (x : M)
    (ξ : Fin n → ℂ) :
    dbarDot n z (fun y => (F0 y - F y) * Complex.exp (Ph y)) x ξ =
      Complex.exp (Ph x) * (dbarDot n z F0 x ξ +
        (F0 x - F x) * dbarDot n z (fun y => (Ph y : ℂ)) x ξ) := by
  have hF0' : Ck n z 1 F0 := Smooth.ck n z 1 F0 hF0
  have hF' : Ck n z 1 F := Smooth.ck n z 1 F (Holo.smooth n z F hF)
  have hPh' : Ck n z 1 (fun y => (Ph y : ℂ)) := Smooth.ck n z 1 _ hPh
  have hsub : Ck n z 1 (fun y => F0 y - F y) := Ck.sub n z 1 F0 F hF0' hF'
  have hexp : Ck n z 1 (fun y => Complex.exp (Ph y : ℂ)) := Ck.cexp n z 1 _ hPh'
  have hdsub : ∀ j, db n z j (fun y => F0 y - F y) x = db n z j F0 x := by
    intro j
    have e1 : (fun y => F0 y - F y) = fun y => F0 y + (-1 : ℂ) * F y := by funext y; ring
    rw [e1, db_add n z _ _ hF0' (Ck.mul n z 1 _ _ (Ck.const n z 1 (-1)) hF') j x,
      db_const_mul n z (-1) F hF' j x, Holo.db_eq_zero n z F hF j x]
    ring
  have hterm : ∀ j, db n z j (fun y => (F0 y - F y) * Complex.exp (Ph y : ℂ)) x =
      Complex.exp (Ph x) * (db n z j F0 x + (F0 x - F x) * db n z j (fun y => (Ph y : ℂ)) x) := by
    intro j
    rw [db_mul n z (fun y => F0 y - F y) (fun y => Complex.exp (Ph y : ℂ)) hsub hexp j x, hdsub j,
      db_cexp n z _ hPh' j x]
    ring
  simp only [dbarDot, hterm, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem twBound (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hH : HStatement n M) : TwBoundStatement n M := by
  intro X ps Ph F0 a b hps hPh hC hlevi hF0 hF0w ha hb ha0 hb0 hA hB F hF
  obtain ⟨C, hC⟩ := hC
  obtain ⟨hFh, hFw, horthF⟩ := hF
  have hz := X.isLocalHomeomorph
  have hF0c : Continuous F0 := Smooth.continuous n X.z hz F0 hF0
  have hFc : Continuous F := Smooth.continuous n X.z hz F (Holo.smooth n X.z F hFh)
  have hPhc : Continuous Ph := Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hPh)
  have hpsc : Continuous ps := Complex.continuous_re.comp (Smooth.continuous n X.z hz _ hps)
  have huc : Continuous (fun x => F0 x - F x) := hF0c.sub hFc
  have hCx : ∀ x, Ph x ≤ C := fun x => (abs_le.mp (hC x)).2
  have hCx' : ∀ x, -C ≤ Ph x := fun x => (abs_le.mp (hC x)).1

  have hF1 : Smooth n X.z (fun y => (F0 y - F y) * Complex.exp (Ph y)) :=
    Smooth.mul n X.z _ _ (Smooth.sub n X.z _ _ hF0 (Holo.smooth n X.z F hFh))
      (Smooth.cexp n X.z _ hPh)
  have hhm : Measurable (fun x => ENNReal.ofReal (Real.exp (2 * Ph x) *
      (Real.sqrt (a x) + ‖F0 x - F x‖ * Real.sqrt (b x)) ^ 2)) :=
    ((Real.continuous_exp.comp (continuous_const.mul hPhc)).measurable.mul
      ((ha.sqrt.add (huc.norm.measurable.mul hb.sqrt)).pow_const 2)).ennreal_ofReal
  have hbound : ∀ (x : M) (ξ : Fin n → ℂ),
      ENNReal.ofReal (‖dbarDot n X.z (fun y => (F0 y - F y) * Complex.exp (Ph y)) x ξ‖ ^ 2) ≤
        ENNReal.ofReal (Real.exp (2 * Ph x) * (Real.sqrt (a x) + ‖F0 x - F x‖ * Real.sqrt (b x)) ^ 2) *
          ENNReal.ofReal (Levi n X.z (fun y => ps y + Ph y) x ξ).re := by
    intro x ξ
    have h1 := twb_pt (Ph x) (a x) (b x) (Levi n X.z (fun y => ps y + Ph y) x ξ).re
      (dbarDot n X.z F0 x ξ) (dbarDot n X.z (fun y => (Ph y : ℂ)) x ξ) (F0 x - F x)
      (ha0 x) (hb0 x) (hlevi x ξ) (hA x ξ) (hB x ξ)
    rw [twb_dbar n X.z F0 F Ph hF0 hFh hPh x ξ, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  obtain ⟨G, hGh, hGw⟩ := hH X (fun y => ps y + Ph y) (fun y => (F0 y - F y) * Complex.exp (Ph y))
    _ (SmoothR.add n X.z _ _ hps hPh) hlevi hF1 hhm hbound

  have hRHS : ∫⁻ x, ENNReal.ofReal (Real.exp (2 * Ph x) *
      (Real.sqrt (a x) + ‖F0 x - F x‖ * Real.sqrt (b x)) ^ 2) *
        ENNReal.ofReal (Real.exp (-(ps x + Ph x))) ∂vol n X.z =
      ∫⁻ x, ENNReal.ofReal ((Real.sqrt (a x) + ‖F0 x - F x‖ * Real.sqrt (b x)) ^ 2 *
        Real.exp (Ph x - ps x)) ∂vol n X.z := by
    congr 1
    funext x
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show Real.exp (Ph x - ps x) = Real.exp (2 * Ph x) * Real.exp (-(ps x + Ph x)) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  by_cases hR : ∫⁻ x, ENNReal.ofReal ((Real.sqrt (a x) + ‖F0 x - F x‖ * Real.sqrt (b x)) ^ 2 *
      Real.exp (Ph x - ps x)) ∂vol n X.z = ⊤
  · rw [hR]; exact le_top
  have hRlt := lt_top_iff_ne_top.mpr hR
  have hGc : Continuous G := Smooth.continuous n X.z hz G (Holo.smooth n X.z G hGh)
  have hw : ∀ x, ‖(F0 x - F x) * Complex.exp (Ph x)‖ ^ 2 * Real.exp (-(ps x + Ph x)) =
      ‖F0 x - F x‖ ^ 2 * Real.exp (Ph x - ps x) := by
    intro x
    have e1 : Real.exp (Ph x) ^ 2 * Real.exp (-(ps x + Ph x)) = Real.exp (Ph x - ps x) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [norm_mul, Complex.norm_exp_ofReal, mul_pow, mul_assoc, e1]
  have hIu : ∫⁻ x, ENNReal.ofReal (‖F0 x - F x‖ ^ 2 * Real.exp (-ps x)) ∂vol n X.z < ⊤ := by
    refine lt_of_le_of_lt (twb_sub_le (vol n X.z) F0 F (fun x => Real.exp (-ps x))
      hF0c.measurable hFc.measurable (Real.continuous_exp.comp hpsc.neg).measurable
      (fun x => (Real.exp_pos _).le)) ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hF0w, ENNReal.mul_lt_top (by simp) hFw⟩
  have hwf : ∫⁻ x, ENNReal.ofReal (‖(F0 x - F x) * Complex.exp (Ph x)‖ ^ 2 *
      Real.exp (-(ps x + Ph x))) ∂vol n X.z < ⊤ := by
    simp_rw [hw]
    refine lt_of_le_of_lt (twb_wmono (vol n X.z) (fun x => ‖F0 x - F x‖ ^ 2)
      (fun x => Real.exp (Ph x - ps x)) (fun x => Real.exp (-ps x)) (Real.exp C)
      (Real.exp_pos _).le (fun x => sq_nonneg _) (fun x => ?_)) (ENNReal.mul_lt_top (by simp) hIu)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [hCx x])
  have hwG : ∫⁻ x, ENNReal.ofReal (‖(F0 x - F x) * Complex.exp (Ph x) - G x‖ ^ 2 *
      Real.exp (-(ps x + Ph x))) ∂vol n X.z < ⊤ := by
    refine lt_of_le_of_lt hGw ?_
    rw [hRHS]; exact hRlt
  have hGf : ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2 * Real.exp (-(ps x + Ph x))) ∂vol n X.z < ⊤ := by
    have e3 : ∀ x, G x = (F0 x - F x) * Complex.exp (Ph x) -
        ((F0 x - F x) * Complex.exp (Ph x) - G x) := fun x => by ring
    simp_rw [fun x => congrArg (fun t => ENNReal.ofReal (‖t‖ ^ 2 * Real.exp (-(ps x + Ph x)))) (e3 x)]
    refine lt_of_le_of_lt (twb_sub_le (vol n X.z) _ _ (fun x => Real.exp (-(ps x + Ph x)))
      (huc.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp hPhc))).measurable
      ((huc.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp hPhc))).sub hGc).measurable
      (Real.continuous_exp.comp (hpsc.add hPhc).neg).measurable (fun x => (Real.exp_pos _).le)) ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hwf, ENNReal.mul_lt_top (by simp) hwG⟩
  have hGps : wint n X.z G ps < ⊤ := by
    refine lt_of_le_of_lt (twb_wmono (vol n X.z) (fun x => ‖G x‖ ^ 2) (fun x => Real.exp (-ps x))
      (fun x => Real.exp (-(ps x + Ph x))) (Real.exp C) (Real.exp_pos _).le (fun x => sq_nonneg _)
      (fun x => ?_)) (ENNReal.mul_lt_top (by simp) hGf)
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [hCx x])
  have horth : ∫ x, (F0 x - F x) * Complex.exp (Ph x) * (starRingEnd ℂ) (G x) *
      ((Real.exp (-(ps x + Ph x)) : ℝ) : ℂ) ∂vol n X.z = 0 := by
    have hpt : ∀ x, (F0 x - F x) * Complex.exp (Ph x) * (starRingEnd ℂ) (G x) *
        ((Real.exp (-(ps x + Ph x)) : ℝ) : ℂ) =
        (F0 x - F x) * (starRingEnd ℂ) (G x) * ((Real.exp (-ps x) : ℝ) : ℂ) := by
      intro x
      have e2 : Complex.exp (Ph x) * ((Real.exp (-(ps x + Ph x)) : ℝ) : ℂ) =
          ((Real.exp (-ps x) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1; push_cast; ring
      calc _ = (F0 x - F x) * (starRingEnd ℂ) (G x) *
            (Complex.exp (Ph x) * ((Real.exp (-(ps x + Ph x)) : ℝ) : ℂ)) := by ring
        _ = _ := by rw [e2]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact horthF G hGh hGps
  have hpyth := twb_pyth (vol n X.z) (fun x => (F0 x - F x) * Complex.exp (Ph x)) G
    (fun x => Real.exp (-(ps x + Ph x)))
    (huc.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp hPhc))).measurable
    hGc.measurable (Real.continuous_exp.comp (hpsc.add hPhc).neg).measurable
    (fun x => (Real.exp_pos _).le) hwf hGf horth
  calc ∫⁻ x, ENNReal.ofReal (‖F0 x - F x‖ ^ 2 * Real.exp (Ph x - ps x)) ∂vol n X.z
      = ∫⁻ x, ENNReal.ofReal (‖(F0 x - F x) * Complex.exp (Ph x)‖ ^ 2 *
          Real.exp (-(ps x + Ph x))) ∂vol n X.z := by simp_rw [hw]
    _ ≤ ∫⁻ x, ENNReal.ofReal (‖(F0 x - F x) * Complex.exp (Ph x) - G x‖ ^ 2 *
          Real.exp (-(ps x + Ph x))) ∂vol n X.z := hpyth
    _ ≤ _ := hGw
    _ = _ := hRHS

end ReciprocityTheory.L2DbarEstimates.I
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.LeviForms.ImportsAlt

section

@[expose] public section

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (hH : HStatement n M) (hC : HoloClosedNeed n M) :
    TWStatement n M := by
  intro X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 _ hA hB
  refine ⟨bergmanExists n M hC X ps F0 hps
    (Smooth.continuous n X.z X.isLocalHomeomorph F0 hF0).measurable hF0w, ?_⟩
  exact twBound n M hH X ps Ph F0 a b hps hPh hCb hlevi hF0 hF0w ha hb ha0 hb0 hA hB

end ReciprocityTheory.L2DbarEstimates.I
end
end
