module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormEqProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierLipschitzOneVariableKernelEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHilbertEisensteinWeightTwoQSeriesStatement
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformSigmaZeroEq

section

@[expose] public section

noncomputable section

open Complex MeasureTheory Set
open scoped FourierTransform

namespace GlobalTheory.HeckeTwo

lemma lipschitzOneVariableKernel_two_eq_indicator {y : ℝ} (hy : 0 < y) :
    GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ 1 * Complex.exp (-(((2 * Real.pi * y : ℝ) : ℂ) * t))) := by
  funext t
  have him : ((y : ℂ) * I).im = y := by simp
  simp only [GlobalTheory.LipschitzTR.phi1, Set.indicator, Set.mem_Ioi, him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases ht : 0 < t
  · rw [if_pos ht, if_pos ht, abs_of_pos ht]
    push_cast
    congr 2
    ring_nf
    rw [I_sq]
    ring
  · rw [if_neg ht, if_neg ht]

lemma norm_inv_ofReal_add_mul_I_sq (x y : ℝ) : ‖((x : ℂ) + (y : ℂ) * I)⁻¹ ^ 2‖ = (x ^ 2 + y ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma ofReal_add_ofReal_mul_I_ne_zero (x : ℝ) {y : ℝ} (hy : 0 < y) : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy.ne' this

theorem hTrans_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y =
    if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  intro ν y hy
  set g := GlobalTheory.LipschitzTR.phi1 2 ((y : ℂ) * I) with hg
  have hw : ((y : ℂ) * I).im ≠ 0 := by simp [hy.ne']
  have hgc : Continuous g := GlobalTheory.LipschitzTR.continuous_lipschitzOneVariableKernel le_rfl hw
  have hgi : Integrable g := by
    rw [hg, lipschitzOneVariableKernel_two_eq_indicator hy, integrable_indicator_iff measurableSet_Ioi]
    exact GlobalTheory.LipschitzTR.integrableOn_pow_mul_cexp_neg 1 (by simp; positivity)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hF : ∀ x : ℝ, 𝓕 g x = -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 := by
    intro x
    rw [hg, GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow 2 le_rfl even_two _ hw x]
    have hne := ofReal_add_ofReal_mul_I_ne_zero (-x) hy
    rw [zpow_neg, zpow_natCast]
    push_cast at hne ⊢
    have : (y : ℂ) * I - x = -(x : ℂ) + y * I := by ring
    rw [this]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have hFi : Integrable (𝓕 g) := by
    have hb : Integrable (fun x : ℝ => ((4 * Real.pi ^ 2 * y ^ 2)⁻¹ : ℝ) * (1 + (x / y) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_div hy.ne').const_mul _
    refine hb.mono' ?_ (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    · rw [show (𝓕 g) = fun x : ℝ => -(4 * (Real.pi : ℂ) ^ 2)⁻¹ * (((-x : ℝ) : ℂ) + (y : ℂ) * I)⁻¹ ^ 2 from funext hF]
      exact Continuous.aestronglyMeasurable
        (continuous_const.mul ((((continuous_ofReal.comp continuous_neg).add continuous_const).inv₀
          (fun x => ofReal_add_ofReal_mul_I_ne_zero (-x) hy)).pow 2))
    · rw [hF, norm_mul, norm_neg, norm_inv, norm_mul, norm_pow, norm_inv_ofReal_add_mul_I_sq]
      simp only [RCLike.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, neg_sq]
      have : y ≠ 0 := hy.ne'
      field_simp <;> ring
  have hinv : 𝓕 (𝓕⁻ g) = g := hgc.fourier_fourierInv_eq hgi hFi
  have hphi : ∀ t : ℝ, phi 0 ((t : ℂ) + (y : ℂ) * I) = -4 * (Real.pi : ℂ) ^ 2 * 𝓕⁻ g t := by
    intro t
    rw [Real.fourierInv_eq_fourier_neg, hF, neg_neg]
    unfold phi
    rw [mul_zero, Complex.cpow_zero, mul_one]
    field_simp
  have hT : hTrans 0 ν y = -4 * (Real.pi : ℂ) ^ 2 * 𝓕 (𝓕⁻ g) ν := by
    unfold hTrans
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1
    funext t
    rw [hphi t, smul_eq_mul]
    push_cast
    ring_nf
  rw [hT, hinv, hg]
  simp only [GlobalTheory.LipschitzTR.phi1]
  have him : ((y : ℂ) * I).im = y := by simp
  rw [him, sign_pos hy, SignType.coe_one, one_mul]
  by_cases hν : 0 < ν
  · rw [if_pos hν, if_pos hν, abs_of_pos hν]
    push_cast
    ring_nf
    rw [I_sq]
    ring_nf
  · rw [if_neg hν, if_neg hν, mul_zero]

end GlobalTheory.HeckeTwo
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformSigmaZeroEqStatement

section

@[expose] public section

open Complex GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y = if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | exact GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | (intros; apply GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinWeightTwoQExpansion

section

@[expose] public section

noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwoExp

variable {F : Type} [Field F] [NumberField F]

theorem hTrans_zero (ν y : ℝ) (hy : y ≠ 0) :
    hTrans 0 ν y = if 0 < ν * y then
      -4 * (Real.pi : ℂ) ^ 2 * ((|ν| : ℝ) : ℂ) * ((Real.exp (-(2 * Real.pi * (ν * y))) : ℝ) : ℂ) else 0 := by
  rcases hy.lt_or_gt with h | h
  · have e := hTrans_zero_neg (-ν) y
    rw [neg_neg] at e
    rw [← e, GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq _ _ (neg_pos.2 h)]
    by_cases hν : 0 < -ν
    · have h2 : 0 < ν * y := by nlinarith
      rw [if_pos hν, if_pos h2, abs_of_neg (by linarith : ν < 0),
        show -(2 * Real.pi * -ν * -y) = -(2 * Real.pi * (ν * y)) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]
  · rw [GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq _ _ h]
    by_cases hν : 0 < ν
    · have h2 : 0 < ν * y := mul_pos hν h
      rw [if_pos hν, if_pos h2, abs_of_pos hν, show 2 * Real.pi * ν * y = 2 * Real.pi * (ν * y) by ring]
    · have h2 : ¬ 0 < ν * y := by nlinarith
      rw [if_neg hν, if_neg h2]

theorem fTerm_zero [IsTotallyReal F] {z : Emb F → ℂ} (hz : z ∈ upperHalf F) {b ν : F} (hb : b ≠ 0) (hν : ν ≠ 0) :
    fTerm 0 z b ν = if ∀ τ : Emb F, 0 < τ (ν * b) then
      (-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ((|(Algebra.norm ℚ ν : ℝ)| : ℝ) : ℂ) * qPow (ν * b) z
      else 0 := by
  have hyτ : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ => mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  unfold fTerm
  simp only [hTrans_zero _ _ (hyτ _)]
  split_ifs with hc
  · have hc' : ∀ τ : Emb F, 0 < τ ν * (τ b * (z τ).im) := fun τ => by
      have := hc τ; rw [map_mul] at this; rw [← mul_assoc]; exact mul_pos this (hz τ)
    rw [Finset.prod_congr rfl fun τ _ => by rw [if_pos (hc' τ)]]
    rw [abs_norm_eq_prod, qPow, Finset.mul_sum, Complex.exp_sum]
    rw [show ((-4 * (Real.pi : ℂ) ^ 2) ^ Fintype.card (Emb F) * ∏ τ : Emb F, ((|τ ν| : ℝ) : ℂ)) *
        ∏ x : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((x (ν * b) : ℂ) * z x)) =
        ∏ τ : Emb F, ((-4 * (Real.pi : ℂ) ^ 2) * ((|τ ν| : ℝ) : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (ν * b) : ℂ) * z τ))) by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; congr 1
    conv_rhs => rw [← Complex.re_add_im (z τ)]
    simp only [map_mul]
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * (τ ν : ℂ) * (τ b : ℂ) * ((z τ).im : ℂ)) * I_sq
  · push_neg at hc
    obtain ⟨τ, hτ⟩ := hc
    have : ¬ 0 < τ ν * (τ b * (z τ).im) := by
      rw [map_mul] at hτ; rw [← mul_assoc]; exact not_lt.2 (mul_nonpos_of_nonpos_of_nonneg hτ (hz τ).le)
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [if_neg this, mul_zero])

theorem bOne_zero_expansion [IsTotallyReal F] (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (hz : z ∈ upperHalf F) :
    Summable (qClass 𝔞 𝔟 2 z) ∧
      (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
        ∑' c, qClass 𝔞 𝔟 2 z c := by
  have hS := GlobalTheory.T.summable_hilbertEisensteinWeightTwoQSeries F 𝔞 𝔟 z hz
  refine ⟨hS, ?_⟩
  have hn : (nrm 𝔞 : ℂ) ≠ 0 := by exact_mod_cast nrm_ne_zero 𝔞
  have hs : ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (dF_pos (F := F)) _).ne'
  have hcK : (cK F 2 : ℂ) = ((dF F ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
    unfold cK; norm_num
  have hL : (cK F 2 : ℂ) * (kFac F 0 * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 0 z) / (omegaFactor 𝔞 : ℂ) ^ 2 =
      (kFac F 0 / (nrm 𝔞 : ℂ)) * bOne 𝔞 𝔟 0 z := by
    rw [hcK, omegaFactor]; push_cast
    push_cast at hs
    field_simp
  rw [hL, bOne, ← tsum_mul_left, tsum_qClass_eq 𝔞 𝔟 z hS]
  refine tsum_congr fun c => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun ν => ?_
  rw [fTerm_zero hz c.out.2.2 ν.2.2]
  split_ifs with hc
  · have hk := kFac_zero_mul (F := F)
    unfold qTerm
    simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one, Complex.ofReal_div]
    linear_combination (((|(Algebra.norm ℚ ν.1 : ℝ)| : ℝ) : ℂ) / (nrm 𝔞 : ℂ) * qPow (ν.1 * c.out.1) z) * hk
  · rw [mul_zero]

theorem bOne_zero_qExpansion : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
    Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * (GlobalTheory.HeckeTwo.kFac F 0 *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * GlobalTheory.HeckeTwo.bOne 𝔞 𝔟 0 z) / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 =
      ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c :=
  fun _ _ _ _ 𝔞 𝔟 z hz => bOne_zero_expansion 𝔞 𝔟 z hz

end GlobalTheory.HeckeTwoExp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinWeightTwoQExpansionStatement

section

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

theorem _root_.GlobalTheory.T.heckeEisenstein_weight_two_qExpansion : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, Summable (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F 2 : ℂ) * (GlobalTheory.HeckeTwo.kFac F 0 * (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) * GlobalTheory.HeckeTwo.bOne 𝔞 𝔟 0 z) / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ 2 = ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c := by
  first | exact @GlobalTheory.HeckeTwoExp.bOne_zero_qExpansion | exact GlobalTheory.HeckeTwoExp.bOne_zero_qExpansion | (intros; apply GlobalTheory.HeckeTwoExp.bOne_zero_qExpansion <;> assumption)
end
end
