module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
public import Mathlib.Analysis.Fourier.FourierTransform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeImageEqLatticeImageTraceDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformRapidDecayStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoKernelPhiLineContinuousIntegrableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZLatticeFractionalIdealRealLatticeImage
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableLipschitzLatticeNormPowSummand
public import Formalism.LatticeTheta.LatticeThetaProofs.LatticeFourierSeries
public import Formalism.LatticeTheta.LatticeThetaProofs.Periodization
public import Formalism.LatticeTheta.LatticeThetaProofs.UnfoldCoeff
public import Formalism.LatticeTheta.ThetaShiftInversion
import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRpowDecayIsBigOCocompact

section

@[expose] public section

open MeasureTheory

theorem GlobalTheory.prod_rpow_decay_isBigO_cocompact : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  intro ι _ g b hb hg
  classical
  choose C hC using hg
  have hC0 : ∀ i, 0 ≤ C i := fun i => by
    have h := hC i 0
    simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  refine Asymptotics.IsBigO.of_bound ((∏ i, C i) * n ^ b) ?_
  have hev : ∀ᶠ v : EuclideanSpace ℝ ι in Filter.cocompact _, 0 < ‖v‖ :=
    tendsto_norm_cocompact_atTop.eventually (Filter.eventually_gt_atTop 0)
  filter_upwards [hev] with v hv
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : v = 0 := Subsingleton.elim _ _
    simp [this] at hv
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) Finset.univ_nonempty
  have hn1 : (1:ℝ) ≤ n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hnorm : ‖v‖ ≤ n * |v i₀| := by
    have h2 : ‖v‖ ^ 2 ≤ (n * |v i₀|) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖v.ofLp i‖ ^ 2 ≤ ∑ _i : ι, |v i₀| ^ 2 := Finset.sum_le_sum fun i _ => by
              rw [Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hi₀ i (Finset.mem_univ _)) 2
        _ = n * |v i₀| ^ 2 := by simp [hn]
        _ ≤ (n * |v i₀|) ^ 2 := by
              rw [mul_pow]; exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hnpos : 0 < n := by linarith
  have hpos : 0 < ‖v‖ / n := by positivity
  have hle : ‖v‖ / n ≤ 1 + |v i₀| := by
    rw [div_le_iff₀ hnpos]; nlinarith [abs_nonneg (v i₀)]
  have hw : (1 + |v i₀|) ^ (-b) ≤ n ^ b * ‖v‖ ^ (-b) := by
    calc (1 + |v i₀|) ^ (-b) ≤ (‖v‖ / n) ^ (-b) := Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
      _ = n ^ b * ‖v‖ ^ (-b) := by
        rw [Real.div_rpow (norm_nonneg _) hnpos.le, Real.rpow_neg hnpos.le, div_inv_eq_mul, mul_comm]
  have hrest : ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖ ≤ ∏ i ∈ Finset.univ.erase i₀, C i :=
    Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => (hC i (v i)).trans
      (mul_le_of_le_one_right (hC0 i)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (v i)]) (by linarith))))
  have h0 : ‖g i₀ (v i₀)‖ ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) :=
    (hC i₀ _).trans (mul_le_mul_of_nonneg_left hw (hC0 i₀))
  have hsplitg := Finset.mul_prod_erase Finset.univ (fun i => ‖g i (v i)‖) (Finset.mem_univ i₀)
  have hsplitC := Finset.mul_prod_erase Finset.univ C (Finset.mem_univ i₀)
  rw [norm_prod, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← hsplitg, ← hsplitC]
  calc ‖g i₀ (v i₀)‖ * ∏ i ∈ Finset.univ.erase i₀, ‖g i (v i)‖
      ≤ C i₀ * (n ^ b * ‖v‖ ^ (-b)) * ∏ i ∈ Finset.univ.erase i₀, C i :=
        mul_le_mul h0 hrest (Finset.prod_nonneg fun i _ => norm_nonneg _)
          (mul_nonneg (hC0 i₀) (mul_nonneg (Real.rpow_nonneg hnpos.le _) (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = C i₀ * (∏ i ∈ Finset.univ.erase i₀, C i) * n ^ b * ‖v‖ ^ (-b) := by ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRpowDecayIsBigOCocompactStatement

section

@[expose] public section

open MeasureTheory


theorem _root_.GlobalTheory.T.prod_rpow_decay_isBigO_cocompact' : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  first | exact @GlobalTheory.prod_rpow_decay_isBigO_cocompact | exact GlobalTheory.prod_rpow_decay_isBigO_cocompact | (intros; apply GlobalTheory.prod_rpow_decay_isBigO_cocompact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeWeightTwoLatticeSum

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeTwo

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem norm_phi_le (σ w : ℂ) (hσ : 0 < σ.re) (c : ℝ) (hc : 0 < c) (hcw : c ≤ |w.im|) :
    ‖phi σ w‖ ≤ ‖w⁻¹ ^ 2‖ * c ^ (-2 * σ.re) := by
  have hw : 0 < ‖w‖ := lt_of_lt_of_le hc (hcw.trans (Complex.abs_im_le_norm w))
  unfold phi
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hre : (-2 * σ).re = -2 * σ.re := by simp
  rw [hre]
  exact Real.rpow_le_rpow_of_nonpos hc (hcw.trans (Complex.abs_im_le_norm w)) (by linarith)

theorem summable_latSum (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : Frac F) (σ : ℂ)
    (hσ : 0 < σ.re) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) (b : F) (hb : b ≠ 0) :
    Summable (fun a : {a : F // a ∈ latM 𝔞} =>
      ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  classical
  have hM : latM 𝔞 ≠ 0 := by
    rw [latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero 𝔞)
  set z' : Emb F → ℂ := fun τ => ((τ b : ℝ) : ℂ) * z τ with hz'
  have hc : ∀ τ : Emb F, 0 < |τ b * (z τ).im| := fun τ =>
    abs_pos.2 (mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne')
  have him : ∀ τ : Emb F, (z' τ).im ≠ 0 := fun τ => by
    have := hc τ
    simp only [hz', Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact abs_pos.1 this
  have hs := GlobalTheory.LipschitzTR.summable_lhsTerm_ideal F (latM 𝔞) hM 2 le_rfl z' him
  have hs' : Summable (fun a : {a : F // a ∈ latM 𝔞} => GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1) := hs
  set C : ℝ := ∏ τ : Emb F, |τ b * (z τ).im| ^ (-2 * σ.re) with hC
  refine Summable.of_norm_bounded ((summable_norm_iff.2 hs').mul_left C) fun a => ?_
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm 2 z' a.1 =
      ∏ τ : Emb F, (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)⁻¹ ^ 2 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lhsTerm
    rw [zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hz', inv_pow, add_comm]
  rw [hl, norm_prod, norm_prod, hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  rw [mul_comm (|τ b * (z τ).im| ^ (-2 * σ.re))]
  refine norm_phi_le σ _ hσ _ (hc τ) (le_of_eq ?_)
  simp

end GlobalTheory.HeckeTwo
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeWeightTwoLatticeSumStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors


theorem _root_.GlobalTheory.T.summable_heckeWeightTwoLatticeSum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 → Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := by
  first | exact @GlobalTheory.HeckeTwo.summable_latSum | exact GlobalTheory.HeckeTwo.summable_latSum | (intros; apply GlobalTheory.HeckeTwo.summable_latSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoPoissonSummationFractionalIdeal

section

@[expose] public section

open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.HeckeTwoPoisson

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.LipschitzTR

theorem hTrans_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ,
    ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := GlobalTheory.T.heckePhiFourierTransform_rapid_decay

theorem phi_line : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 →
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
    Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := GlobalTheory.T.heckeWeightTwoKernelPhi_line_continuous_integrable

theorem summable_lat : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 →
    Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} =>
      ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ)) := GlobalTheory.T.summable_heckeWeightTwoLatticeSum

theorem prod_isBigO : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b →
    (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) →
    (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)]
      (fun v => ‖v‖ ^ (-b)) := GlobalTheory.T.prod_rpow_decay_isBigO_cocompact'

theorem fourier_prod (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.fourier_real_eq]
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul]

theorem remb_inj {F : Type} [Field F] [NumberField F] [IsTotallyReal F] : Function.Injective (remb F) := by
  intro a b h
  have hne : Nonempty (F →+* ℝ) := by
    rw [← Fintype.card_pos_iff, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb]
    exact Module.finrank_pos
  have h1 := congrArg (fun v : RSp F => v (Classical.choice hne)) h
  simp only [remb_apply] at h1
  exact (Classical.choice hne).injective h1

theorem hTrans_eq_fourier (σ : ℂ) (y : ℝ) :
    (fun ν : ℝ => hTrans σ ν y) = 𝓕 (fun t : ℝ => phi σ ((t : ℂ) + (y : ℂ) * I)) := by
  funext ν
  rw [Real.fourier_real_eq]
  unfold hTrans
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [smul_eq_mul, Real.fourierChar_apply]
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem continuous_hTrans (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun ν : ℝ => hTrans σ ν y) := by
  rw [hTrans_eq_fourier]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (phi_line σ hσ y hy).2

theorem fourier_mod (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) (c s : ℝ) :
    𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      phi σ (((c - s : ℝ) : ℂ) + (y : ℂ) * I) := by
  set f : ℝ → ℂ := fun t => phi σ ((t : ℂ) + (y : ℂ) * I) with hf
  obtain ⟨hfc, hfi⟩ := phi_line σ hσ y hy
  have hH := hTrans_eq_fourier σ y
  have hFi : Integrable (𝓕 f) := by
    obtain ⟨C, hC⟩ := hTrans_decay σ hσ y hy 2
    have h2 : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
      integrable_one_add_norm (by simp)
    refine (h2.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
    · rw [← hH]; exact (continuous_hTrans σ hσ y hy).aestronglyMeasurable
    · have := hC t
      rw [← hH]
      simpa [Real.norm_eq_abs] using this
  have hinv : 𝓕⁻ (𝓕 f) = f := Continuous.fourierInv_fourier_eq hfc hfi hFi
  have hmod : 𝓕 (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * c : ℝ) : ℂ)) * hTrans σ t y) s =
      𝓕 (𝓕 f) (s - c) := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← hH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hmod]
  have h3 := congrFun hinv (-(s - c))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h3
  rw [h3, hf]
  congr 2
  push_cast
  ring

theorem poisson : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (σ : ℂ),
    0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ b : F, b ≠ 0 →
    Summable (fun ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)} => GlobalTheory.HeckeTwo.fTerm σ z b ν.1) ∧
    HasSum (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => ∏ τ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, GlobalTheory.HeckeTwo.phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ))
      ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * ∑' ν : {ν : F // ν ∈ (𝔞 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)}, GlobalTheory.HeckeTwo.fTerm σ z b ν.1) := by
  intro F _ _ _ 𝔞 σ hσ z hz b hb
  classical
  set A : FractionalIdeal (𝓞 F)⁰ F := (𝔞 : FractionalIdeal (𝓞 F)⁰ F) with hA
  have hA0 : A ≠ 0 := 𝔞.ne_zero
  haveI : DiscreteTopology (latOf A) := discrete_latOf F A
  haveI : IsZLattice ℝ (latOf A) := isZLattice_latOf F A hA0
  set L := latOf A with hL
  have hdual : Formalism.H.dual L = latOf (latM 𝔞) := by
    rw [hL, dual_latOf_eq_latOf_traceDual F A hA0, latM_eq_dual]
  have hcov : ZLattice.covolume L = omegaFactor 𝔞 := by
    rw [hL, GlobalTheory.LipschitzCovol.covolume_latOf F A hA0, GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol, omegaFactor, dF, nrm,
      Real.sqrt_eq_rpow]
  obtain ⟨h1, h2⟩ := Formalism.H.dualIsLattice (RSp F) L
  haveI : DiscreteTopology (Formalism.H.dual L) := h1

  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  set g : Emb F → ℝ → ℂ := fun τ t =>
    Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) * hTrans σ t (τ b * (z τ).im) with hg
  set Ψ : RSp F → ℂ := fun v => ∏ τ, g τ (v τ) with hΨ
  have hΨν : ∀ ν : F, Ψ (remb F ν) = fTerm σ z b ν := by
    intro ν
    simp only [hΨ, hg, remb_apply, fTerm]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 3
    push_cast
    ring
  have hgn : ∀ τ t, ‖g τ t‖ = ‖hTrans σ t (τ b * (z τ).im)‖ := by
    intro τ t
    simp only [hg, norm_mul]
    rw [show (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ)) =
      ((2 * Real.pi * (t * (τ b * (z τ).re)) : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hΨc : Continuous Ψ := by
    refine continuous_finsetProd _ fun τ _ => ?_
    refine Continuous.comp (g := g τ) ?_ ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
    exact (by fun_prop : Continuous fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * I * ((t * (τ b * (z τ).re) : ℝ) : ℂ))).mul
      (continuous_hTrans σ hσ _ (hyτ τ))
  set N : ℕ := Module.finrank ℝ (RSp F) + 1 with hN
  have hbN : (Module.finrank ℝ (RSp F) : ℝ) < (N : ℝ) := by rw [hN]; push_cast; linarith
  have hΨO : Ψ =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-(N : ℝ)) :=
    prod_isBigO (Emb F) g N (Nat.cast_nonneg _) fun τ => by
      obtain ⟨C, hC⟩ := hTrans_decay σ hσ _ (hyτ τ) N
      exact ⟨C, fun t => (hgn τ t).symm ▸ hC t⟩
  obtain ⟨hint, hsumx, hGc, hGper⟩ := Formalism.H.poisson_periodization (RSp F) L Ψ hΨc (N : ℝ) hbN hΨO
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hD := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 Ψ μ :=
    fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L Ψ hint D hD μ μ.2

  have hFΨ : ∀ a : F, 𝓕 Ψ (remb F (-a)) = ∏ τ : Emb F, phi σ (((τ a : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ) := by
    intro a
    rw [hΨ, fourier_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [remb_apply, hg]
    simp only
    rw [fourier_mod σ hσ _ (hyτ τ)]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ latM 𝔞, remb F a = x := by
    intro x; rw [hdual]; exact mem_latOf _ x
  have hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ A, remb F ν = x := by
    intro x; rw [hL]; exact mem_latOf _ x
  let eM : {a : F // a ∈ latM 𝔞} ≃ Formalism.H.dual L := Equiv.ofBijective
    (fun a => ⟨remb F (-a.1), (hDmem _).2 ⟨-a.1, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem a.2, rfl⟩⟩)
    ⟨fun a a' h => Subtype.ext (neg_injective (remb_inj (congrArg Subtype.val h))), fun μ => by
      obtain ⟨a, ha, h⟩ := (hDmem μ).1 μ.2
      exact ⟨⟨-a, (latM 𝔞 : Submodule (𝓞 F) F).neg_mem ha⟩, Subtype.ext (by simp [h])⟩⟩
  let eD : {ν : F // ν ∈ A} ≃ L := Equiv.ofBijective
    (fun ν => ⟨remb F ν.1, (hLmem _).2 ⟨ν.1, ν.2, rfl⟩⟩)
    ⟨fun ν ν' h => Subtype.ext (remb_inj (congrArg Subtype.val h)), fun μ => by
      obtain ⟨ν, hν, h⟩ := (hLmem μ).1 μ.2
      exact ⟨⟨ν, hν⟩, Subtype.ext h⟩⟩
  have hsL := summable_lat F 𝔞 σ hσ z hz b hb
  have hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Ψ ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) := by
    simp only [hcoef]
    rw [← eM.summable_iff]
    exact hsL.congr fun a => (hFΨ a.1).symm
  have H4 := Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Ψ ((l : RSp F) + x))
    hGc hGper D hD hsumc 0
  simp only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    add_zero] at H4
  rw [← eM.hasSum_iff] at H4
  have hs0 : Summable (fun l : L => Ψ (l : RSp F)) := by simpa using hsumx 0
  have hsF : Summable (fun ν : {ν : F // ν ∈ A} => fTerm σ z b ν.1) := by
    rw [← eD.summable_iff] at hs0
    exact hs0.congr fun ν => hΨν ν.1
  have hR : ∑' l : L, Ψ (l : RSp F) = ∑' ν : {ν : F // ν ∈ A}, fTerm σ z b ν.1 := by
    rw [← eD.tsum_eq]
    exact tsum_congr fun ν => hΨν ν.1
  refine ⟨hsF, ?_⟩
  have hc0 : (ZLattice.covolume L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ZLattice.covolume_ne_zero L volume)
  have H5 := H4.mul_left (ZLattice.covolume L : ℂ)
  rw [hR] at H5
  rw [← hcov]
  refine H5.congr_fun fun a => ?_
  have key : ∀ a : {a : F // a ∈ latM 𝔞}, 𝓕 Ψ ((eM a : RSp F)) = ∏ τ : Emb F, phi σ (((τ a.1 : ℝ) : ℂ) + ((τ b : ℝ) : ℂ) * z τ) :=
    fun a => hFΨ a.1
  simp only [Function.comp_apply, key]
  rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

end GlobalTheory.HeckeTwoPoisson
end
end
end
