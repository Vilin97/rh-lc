module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanIntegrable
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartBergmanBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartTaylorCover
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexTaylor
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralOfBergman
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartBergman
import Mathlib.Tactic.Lemma
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUniformBergmanBound
import Mathlib.Tactic.Linter.Style

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBis

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology

theorem L1Convergence.proof : L1Convergence.Statement := by
  intro Ω _ μ _ g b C hg hb hC hlim hint

  have hp_int : ∀ n, Integrable (fun x => max (g n x - b x) 0) μ :=
    fun n => ((hg n).sub hb).pos_part
  have hbound_int : Integrable (fun x => C + |b x|) μ := (integrable_const C).add hb.abs
  have hpt : Tendsto (fun n => ∫ x, max (g n x - b x) 0 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun n x => max (g n x - b x) 0) (f := fun _ => (0 : ℝ)) (fun x => C + |b x|)
      (fun n => (hp_int n).aestronglyMeasurable) hbound_int
      (fun n => Filter.Eventually.of_forall fun x => by
        have h1 := hC n x
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [neg_abs_le (b x)]) (by linarith [abs_nonneg (b x)]))
      (Filter.Eventually.of_forall fun x => by
        refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
          lt_of_lt_of_le ha (le_max_right _ _), fun a ha => ?_⟩
        filter_upwards [hlim x (a / 2) (by linarith)] with n hn
        exact lt_of_le_of_lt (max_le (show g n x - b x ≤ a / 2 by linarith)
          (show (0 : ℝ) ≤ a / 2 by linarith)) (by linarith))
    simpa using h

  have hid : ∀ n, ∫ x, |g n x - b x| ∂μ =
      2 * ∫ x, max (g n x - b x) 0 ∂μ - (∫ x, g n x ∂μ - ∫ x, b x ∂μ) := by
    intro n
    have hpt' : ∀ x, |g n x - b x| = 2 * max (g n x - b x) 0 - (g n x - b x) := by
      intro x
      rcases le_total 0 (g n x - b x) with h | h
      · rw [abs_of_nonneg h, max_eq_left h]; ring
      · rw [abs_of_nonpos h, max_eq_right h]; ring
    simp_rw [hpt']
    have hgb : Integrable (fun x => g n x - b x) μ := (hg n).sub hb
    rw [integral_sub ((hp_int n).const_mul 2) hgb, integral_const_mul,
      integral_sub (hg n) hb]
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun n =>
    lt_of_lt_of_le ha (integral_nonneg fun x => abs_nonneg _), fun a ha => ?_⟩
  filter_upwards [(tendsto_order.1 hpt).2 (a / 4) (by linarith), hint (a / 4) (by linarith)]
    with n hn1 hn2
  rw [hid n]
  linarith

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexTaylorTwo

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric

noncomputable section

theorem taylor_two_isLittleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun z => f (x + z) - f x - fderiv ℝ f x z - fderiv ℝ (fderiv ℝ f) x z z / 2)
      =o[𝓝 0] fun z => ‖z‖ ^ 2 := by
  set L := fderiv ℝ f x
  set H := fderiv ℝ (fderiv ℝ f) x with hHdef
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  have hH : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.1 hH
  have htend : Tendsto (fun z : E => x + z) (𝓝 0) (𝓝 x) := by
    have : Continuous fun z : E => x + z := continuous_const.add continuous_id
    simpa using this.tendsto (0 : E)
  have hdiff : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℝ f (x + z) :=
    htend.eventually ((hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp))
  refine isLittleO_iff.2 fun ε hε => ?_
  have hb := (isLittleO_iff.1 ho hε).and hdiff
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hb
  filter_upwards [ball_mem_nhds (0 : E) hδ] with z hz
  set g : E → ℝ := fun w => f (x + w) - f x - L w - (2 : ℝ)⁻¹ • H w w with hg
  have hderiv : ∀ w ∈ ball (0 : E) δ, HasFDerivAt g (fderiv ℝ f (x + w) - L - H w) w := by
    intro w hw
    have h1 : HasFDerivAt (fun w => f (x + w)) ((fderiv ℝ f (x + w)).comp
        (ContinuousLinearMap.id ℝ E)) w :=
      (hball w hw).2.hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x)
    have h2 : HasFDerivAt (fun w => H w w) ((H w).comp (ContinuousLinearMap.id ℝ E) + H.flip w) w :=
      H.hasFDerivAt.clm_apply (hasFDerivAt_id w)
    have h3 := ((h1.sub_const (f x)).sub L.hasFDerivAt).sub (h2.const_smul (2 : ℝ)⁻¹)
    refine h3.congr_fderiv ?_
    ext v
    simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    have := hsymm v w
    rw [← hHdef] at this
    rw [this]
    ring
  have hz' : ‖z‖ < δ := by simpa using hz
  have hsub : closedBall (0 : E) ‖z‖ ⊆ ball 0 δ := closedBall_subset_ball hz'
  have hbound : ∀ w ∈ closedBall (0 : E) ‖z‖, ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖z‖ := by
    intro w hw
    have hw' := (hball w (hsub hw)).1
    have hwz : ‖w‖ ≤ ‖z‖ := by simpa using hw
    calc ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖w‖ := hw'
      _ ≤ ε * ‖z‖ := by gcongr
  have hz0 : z ∈ closedBall (0 : E) ‖z‖ := by simp
  have hmvt := (convex_closedBall (0 : E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw => (hderiv w (hsub hw)).hasFDerivWithinAt) hbound
    (mem_closedBall_self (norm_nonneg z)) hz0
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero] at hmvt
  have : g z = f (x + z) - f x - L z - H z z / 2 := by
    simp only [hg, smul_eq_mul]; ring
  rw [← this, norm_pow, norm_norm]
  calc ‖g z‖ ≤ ε * ‖z‖ * ‖z‖ := hmvt
    _ = ε * ‖z‖ ^ 2 := by ring

def complexLinearCoeffs {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) : Fin D → ℂ :=
  fun j => (L (Pi.single j 1) : ℂ) - Complex.I * (L (Complex.I • Pi.single j 1) : ℂ)

theorem re_complexLinearCoeffs_dot {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (complexLinearCoeffs L ⬝ᵥ z).re = L z := by
  have hz : z = ∑ j, ((z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ))) := by
    ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  conv_rhs => rw [hz]

  simp only [map_sum, map_add (f := _), map_smul, dotProduct, Complex.re_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [complexLinearCoeffs, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

def complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun j k =>
    let ej : Fin D → ℂ := Pi.single j 1
    let ek : Fin D → ℂ := Pi.single k 1
    ((H ej ek - H (Complex.I • ej) (Complex.I • ek) : ℝ) -
      Complex.I * ((H ej (Complex.I • ek) + H (Complex.I • ej) ek : ℝ))) / 4

theorem re_dot_complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (z : Fin D → ℂ) :
    (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re = (H z z - H (Complex.I • z) (Complex.I • z)) / 4 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin D → (Fin D → ℂ), c = fun j => (z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin D → (Fin D → ℂ), d = fun j =>
      (z j).re • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) +
      (-(z j).im) • (Pi.single j 1 : Fin D → ℂ) := ⟨_, rfl⟩
  have hz : z = ∑ j, c j := by
    rw [hc]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have hIz : Complex.I • z = ∑ j, d j := by
    rw [hd]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have expand : ∀ c : Fin D → (Fin D → ℂ),
      H (Finset.sum Finset.univ c) (Finset.sum Finset.univ c) = ∑ i, ∑ k, H (c i) (c k) := by
    intro c

    simp only [map_sum, _root_.sum_apply]
    rw [Finset.sum_comm]
  have e1 : H z z = ∑ i, ∑ k, H (c i) (c k) := by
    calc H z z = H (∑ j, c j) (∑ j, c j) := by rw [← hz]
      _ = _ := expand c
  have e2 : H (Complex.I • z) (Complex.I • z) = ∑ i, ∑ k, H (d i) (d k) := by
    rw [hIz]; exact expand d
  have hR : (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re =
      ∑ i, ∑ k, (z i * (complexQuadMatrix H i k * z k)).re := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
  rw [hR, e1, e2, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  subst hc hd
  simp only [map_add (f := _), map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [complexQuadMatrix, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem ComplexTaylorTwo.proof : ComplexTaylorTwo.Statement := by
  intro D ψ y₀ hψ
  refine ⟨complexLinearCoeffs (fderiv ℝ ψ y₀), complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀), ?_⟩
  refine (taylor_two_isLittleO hψ).congr_left fun z => ?_
  have h1 := re_complexLinearCoeffs_dot (fderiv ℝ ψ y₀) z
  have h2 := re_dot_complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀) z
  have h3 := ReciprocityTheory.AnForm.M.re_star_dot_hessC ψ y₀ (star z)
  rw [star_star] at h3
  rw [Complex.add_re, h1, h2, h3]
  unfold levi
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalBergmanBound

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ContDiff

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

lemma mem_source_chartIdx (A : FinHolAtlas D X) (x : X) : x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

lemma target_inter_symm_source (A : FinHolAtlas D X) (j : Fin A.n) :
    (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source = (A.chart j).target :=
  inter_eq_left.2 fun _ hy => (A.chart j).map_target hy

theorem LocalBergmanBound.proof (hC : ChartBergmanBound.Statement) :
    LocalBergmanBound.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV x ε hε
  have := dV.isProb
  set k := chartIdx A x with hk
  set e := A.chart k with he
  have hx : x ∈ e.source := mem_source_chartIdx A x
  have hy0 : e x ∈ e.target := e.map_source hx
  have hψ : ContDiffOn ℝ ∞ (W.φ k ∘ e.symm) e.target := by
    have := W.smooth k k
    rwa [target_inter_symm_source] at this
  have hmain := hC D e.target (W.φ k ∘ e.symm) (dV.dens k) (e x) e.open_target hy0
    (hψ.of_le (WithTop.coe_le_coe.2 le_top)) ((dV.smooth k).continuousOn) (dV.pos k _ hy0)
    (fun w => hW k (e x) hy0 w) ε hε
  have hb : bergmanDens W dV x =
      (((1 / Real.pi : ℝ) : ℂ) • hessC (W.φ k ∘ e.symm) (e x)).det.re / dV.dens k (e x) := by
    have hD : (D.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
    exact mul_div_mul_left _ _ hD
  filter_upwards [hmain] with n hn
  rw [← hb] at hn
  set K := (bergmanDens W dV x + ε) * (n : ℝ) ^ D with hK

  have hKpos : 0 < K := by
    by_contra hle
    have h1 := hn (fun _ => 1) analyticOnNhd_const
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 hle), zero_mul, nonpos_iff_eq_zero,
      ENNReal.ofReal_eq_zero] at h1
    have : 0 < ‖(1 : ℂ)‖ ^ 2 * Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) := by
      simp [Real.exp_pos]
    linarith
  refine ciSup_le fun s => ?_
  have hs : (s : Fin A.n → X → ℂ) ∈ L.sections n := hV n s.2
  have hcont := continuous_ptNormSq W hs
  have hnn : ∀ z, 0 ≤ ptNormSq W n s z := ptNormSq_nonneg W n s
  have hint : Integrable (ptNormSq W n s) dV.μ := integrable_ptNormSq W dV hs
  have hl2 : 0 ≤ sectionL2NormSq W dV n s := sectionL2NormSq_nonneg W dV n s

  have hF : AnalyticOnNhd ℂ ((s : Fin A.n → X → ℂ) k ∘ e.symm) e.target := by
    have := hs.1 k k
    rwa [target_inter_symm_source] at this
  have h1 := hn _ hF
  have hleft : ‖((s : Fin A.n → X → ℂ) k ∘ e.symm) (e x)‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) (e x)) = ptNormSq W n s x := by
    simp only [Function.comp, e.left_inv hx]
    rfl
  have hright : ∫⁻ y in e.target, ENNReal.ofReal (‖((s : Fin A.n → X → ℂ) k ∘ e.symm) y‖ ^ 2 *
      Real.exp (-(n : ℝ) * (W.φ k ∘ e.symm) y) * dV.dens k y) ≤
        ENNReal.ofReal (sectionL2NormSq W dV n s) := by
    have hmeas : Measurable fun z => ENNReal.ofReal (ptNormSq W n s z) :=
      hcont.measurable.ennreal_ofReal
    calc _ = ∫⁻ y in e.target, ENNReal.ofReal (ptNormSq W n s (e.symm y)) *
          ENNReal.ofReal (dV.dens k y) := by
          refine setLIntegral_congr_fun e.open_target.measurableSet fun y hy => ?_
          rw [← ENNReal.ofReal_mul (hnn _), ptNormSq_eq_of_mem W hs k (e.map_target hy)]
          rfl
      _ = ∫⁻ z in e.source, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ :=
          (dV.chart_lintegral k _ hmeas).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (ptNormSq W n s z) ∂dV.μ := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (sectionL2NormSq W dV n s) :=
          (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)).symm
  rw [hleft] at h1
  have h2 : ENNReal.ofReal (ptNormSq W n s x) ≤ ENNReal.ofReal (K * sectionL2NormSq W dV n s) := by
    rw [ENNReal.ofReal_mul hKpos.le]
    exact h1.trans (by gcongr)
  have h3 : ptNormSq W n s x ≤ K * sectionL2NormSq W dV n s :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKpos.le hl2)).1 h2
  rcases hl2.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; exact hKpos.le
  · exact (div_le_iff₀ hpos).2 h3

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.BergmanLerpSelf

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

lemma bergman_lerp_self {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (t : ℝ) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) :
    bergman (W.lerp W t) dV V n x = bergman W dV V n x := by
  simp only [bergman, sectionL2NormSq, ptNormSq, lerp_self_φ]

lemma bergman_nonneg {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    {A : FinHolAtlas D X} {L : HolLineBundle A} (W : Weight L) (dV : SmoothVolume A)
    (V : Submodule ℂ (Fin A.n → X → ℂ)) (n : ℕ) (x : X) : 0 ≤ bergman W dV V n x :=
  Real.iSup_nonneg fun _ => div_nonneg (ptNormSq_nonneg W n _ x) (sectionL2NormSq_nonneg W dV n _)

theorem BergmanL1Convergence.proof (hL1 : L1Convergence.Statement)
    (hLoc : LocalBergmanBound.Statement) (hUnif : UniformBergmanBound.Statement)
    (hInt : IntegralOfBergman.Statement) (hBI : BergmanIntegrable.Statement)
    (hDI : BergmanDensIntegrable.Statement) : BergmanL1Convergence.Statement := by
  intro D X _ _ _ _ _ A L W dV hW V _ hV hdim
  have := dV.isProb
  obtain ⟨C, hC⟩ := hUnif A L W W dV hW hW
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ D := fun n => by positivity
  set g : ℕ → X → ℝ := fun n x =>
    (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x with hg
  have hbound : ∀ n x, 0 ≤ g n x ∧ g n x ≤ C := fun n x => by
    refine ⟨mul_nonneg (inv_nonneg.2 (hpos n).le) (bergman_nonneg _ _ _ _ _), ?_⟩
    have h := hC (n + 1) (by omega) 0 ⟨le_rfl, zero_le_one⟩ (V (n + 1)) (hV _) x
    rw [bergman_lerp_self] at h
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ C
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm C (((n + 1 : ℕ) : ℝ) ^ D)]
  have hlim : ∀ (x : X) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ bergmanDens W dV x + ε := by
    intro x ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hLoc A L W dV hW V hV x ε hε)
    filter_upwards [h] with n hn
    show (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * bergman W dV (V (n + 1)) (n + 1) x ≤ _
    rw [inv_mul_le_iff₀ (hpos n)]
    linarith [mul_comm (bergmanDens W dV x + ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hmass : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∫ x, bergmanDens W dV x ∂dV.μ - ε ≤ ∫ x, g n x ∂dV.μ := by
    intro ε hε
    have h := (tendsto_add_atTop_nat 1).eventually (hdim ε hε)
    filter_upwards [h] with n hn
    have hI : ∫ x, g n x ∂dV.μ =
        (((n + 1 : ℕ) : ℝ) ^ D)⁻¹ * Module.finrank ℂ (V (n + 1)) := by
      rw [hg, integral_const_mul, hInt A L W dV (n + 1) (V (n + 1)) (hV _)]
    rw [hI, le_inv_mul_iff₀ (hpos n)]
    linarith [mul_comm (∫ x, bergmanDens W dV x ∂dV.μ - ε) (((n + 1 : ℕ) : ℝ) ^ D)]
  have hgi : ∀ n, Integrable (g n) dV.μ := fun n =>
    (hBI A L W dV (n + 1) (V (n + 1)) (hV _)).const_mul _
  have h := hL1 dV.μ g (bergmanDens W dV) C hgi (hDI A L W dV) hbound hlim hmass
  exact (tendsto_add_atTop_iff_nat 1).1 h

theorem BergmanL1Convergence.full : BergmanL1Convergence.Statement :=
  BergmanL1Convergence.proof L1Convergence.proof
    (LocalBergmanBound.proof (ChartBergmanBound.proof PolydiscSubmean.proof ComplexTaylorTwo.proof))
    (UniformBergmanBound.proof PolydiscSubmean.proof ChartTaylorCover.proof)
    IntegralOfBergman.proof BergmanIntegrable.proof BergmanDensIntegrable.proof

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end
