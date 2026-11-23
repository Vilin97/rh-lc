module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepNeZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzConstantInverseDifferentEisenstein

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.LipEisConst

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

theorem absNorm_latM {F : Type} [Field F] [NumberField F] (𝔞 : Frac F) :
    ((FractionalIdeal.absNorm (latM 𝔞) : ℚ) : ℝ) = (dF F * nrm 𝔞)⁻¹ := by
  rw [latM, map_mul, map_inv₀, Units.val_inv_eq_inv_val, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal F (𝓞 F), dF, nrm]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, mul_inv]

theorem lip_const_eis : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 1 ≤ k →
    ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lipConst k (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℂ) ^ (k - 1) = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) := by
  intro F _ _ 𝔞 k hk
  have hd : 0 < dF F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hn : 0 < nrm 𝔞 := by
    have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
    have h3 := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) h2.symm
    unfold nrm; exact_mod_cast h3
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F) ≠ 0 := by
    apply pow_ne_zero
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  have hcov : covol (latM 𝔞) = (Real.sqrt (dF F) * nrm 𝔞)⁻¹ := by
    rw [covol, absNorm_latM, ← dF]
    have hs : Real.sqrt (dF F) * Real.sqrt (dF F) = dF F := Real.mul_self_sqrt hd.le
    have hs0 : 0 < Real.sqrt (dF F) := Real.sqrt_pos.2 hd
    field_simp
    rw [Real.sq_sqrt hd.le]

  set fac : ℝ := ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F with hfac
  have hfac0 : 0 < fac := by positivity
  have hreal : nrm 𝔞 ^ (k - 1) / (fac * covol (latM 𝔞)) = omegaFactor 𝔞 ^ k / cK F k := by
    rw [hcov, omegaFactor, cK, ← hfac, mul_pow, ← Real.rpow_natCast (dF F ^ ((1:ℝ)/2)), ← Real.rpow_mul hd.le,
      Real.sqrt_eq_rpow]
    have hk' : ((k : ℝ) - 1) / 2 = (1:ℝ)/2 * k - 1/2 := by ring
    rw [hk', Real.rpow_sub hd]
    have hA : 0 < dF F ^ ((1:ℝ)/2 * k) := Real.rpow_pos_of_pos hd _
    have hB : 0 < dF F ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hd _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have hc : (covol (latM 𝔞) : ℂ) ≠ 0 := by
    rw [hcov]; exact_mod_cast (inv_pos.2 (mul_pos (Real.sqrt_pos.2 hd) hn)).ne'
  have hf : (fac : ℂ) ≠ 0 := by exact_mod_cast hfac0.ne'
  calc _ = (((nrm 𝔞 ^ (k - 1) / (fac * covol (latM 𝔞)) : ℝ)) : ℂ) := by
        rw [lipConst, hfac]; push_cast
        rw [hfac] at hf; push_cast at hf
        field_simp
    _ = _ := by rw [hreal]; push_cast; rfl

end GlobalTheory.LipEisConst
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzConstantInverseDifferentEisensteinStatement

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.lipschitzConstant_inverseDifferent_eisenstein : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 1 ≤ k →
    ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.lipConst k (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) *
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔞 : ℂ) ^ (k - 1) = (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) := by
  first | exact @GlobalTheory.LipEisConst.lip_const_eis | exact GlobalTheory.LipEisConst.lip_const_eis | (intros; apply GlobalTheory.LipEisConst.lip_const_eis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualSignedPositiveConeIffTotallyPositive

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.Div.LipschitzCone

theorem sign_cone_iff (x y w : ℝ) (hx : x ≠ 0) (hw : 0 < w) :
    0 < (SignType.sign (x * w) : ℝ) * y ↔ 0 < y * x := by
  rw [sign_mul, sign_pos hw, mul_one]
  rcases lt_or_gt_of_ne hx with h | h
  · rw [sign_neg h]
    simp only [SignType.coe_neg, SignType.coe_one, neg_mul, one_mul, Left.neg_pos_iff]
    constructor
    · intro hy; exact mul_pos_of_neg_of_neg hy h
    · intro hyx
      by_contra hc
      push_neg at hc
      have := mul_nonpos_of_nonneg_of_nonpos hc h.le
      linarith
  · rw [sign_pos h]
    simp only [SignType.coe_one, one_mul]
    constructor
    · intro hy; exact mul_pos hy h
    · intro hyx; exact pos_of_mul_pos_left hyx h.le

theorem cone_iff : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ ν : F,
      ν ∈ GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) (fun τ => ((τ b : ℝ) : ℂ) * z τ) ↔
        (ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)) := by
  intro F _ _ 𝔞 b hb z hz ν
  have ha : (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔞.ne_zero
  have hM : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 ≠ 0 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]
    exact FractionalIdeal.dual_ne_zero ℤ ℚ ha
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone
  simp only [Set.mem_setOf_eq]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff hM, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.dual_dual]
  refine and_congr Iff.rfl (forall_congr' fun τ => ?_)
  rw [Complex.im_ofReal_mul, map_mul τ ν b]
  exact sign_cone_iff _ _ _ ((map_ne_zero τ).2 hb) (hz τ)

end GlobalTheory.Div.LipschitzCone
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualSignedPositiveConeIffTotallyPositiveStatement

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.mem_traceDualSignedPositiveCone_iff_totallyPositive : ∀ (F : Type) [Field F] [NumberField F] (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∀ ν : F,
      ν ∈ GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.dualCone (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞) (fun τ => ((τ b : ℝ) : ℂ) * z τ) ↔
        (ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ τ : F →+* ℝ, 0 < τ (ν * b)) := by
  first | exact @GlobalTheory.Div.LipschitzCone.cone_iff | exact GlobalTheory.Div.LipschitzCone.cone_iff | (intros; apply GlobalTheory.Div.LipschitzCone.cone_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSumEqConeSum

section

@[expose] public section

open NumberField
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.EisPerB
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

theorem latM_ne_zero (𝔞 : Frac F) : latM 𝔞 ≠ 0 := by
  rw [latM_eq_dual]
  exact FractionalIdeal.dual_ne_zero ℤ ℚ 𝔞.ne_zero

theorem nrm_pos (𝔞 : Frac F) : 0 < nrm 𝔞 := by
  unfold nrm
  have h2 : FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]; exact 𝔞.ne_zero
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) h2.symm

theorem eisTerm_eq [IsTotallyReal F] (k : ℕ) (z : Emb F → ℂ) (a b : F) :
    eisTerm k 0 z (a, b) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      lhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) a := by
  have hprod : ∏ τ, latPt z (a, b) τ = (2 * (Real.pi : ℂ) * Complex.I) ^ (Module.finrank ℚ F) *
      ∏ τ : F →+* ℝ, (((τ b : ℝ) : ℂ) * z τ + ((τ a : ℝ) : ℂ)) := by
    rw [← card_realEmb, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp only [latPt]; ring
  unfold eisTerm lhsTerm
  rw [hprod]
  simp only [mul_zero, Complex.cpow_zero, mul_one, zpow_neg, zpow_natCast]
  ring

theorem rhsTerm_eq [IsTotallyReal F] (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (ν b : F) :
    rhsTerm k (fun τ => ((τ b : ℝ) : ℂ) * z τ) ν = (nrm 𝔞 : ℂ) ^ (k - 1) * qTerm 𝔞 k z (ν, b) := by
  have hN : ∏ τ : F →+* ℝ, τ ν = ((Algebra.norm ℚ ν : ℚ) : ℝ) := by
    have h := prod_emb ν
    rw [← Complex.ofReal_prod] at h
    exact_mod_cast h
  have hpos := nrm_pos 𝔞
  have hreal : |((Algebra.norm ℚ ν : ℚ) : ℝ)| ^ (k - 1) =
      nrm 𝔞 ^ (k - 1) * (|((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞) ^ (k - 1) := by
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hpos.ne')]
  have hsum : ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * (((τ b : ℝ) : ℂ) * z τ) =
      ∑ τ : F →+* ℝ, ((τ (ν * b) : ℝ) : ℂ) * z τ := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [map_mul, Complex.ofReal_mul, mul_assoc]
  unfold rhsTerm qTerm qPow
  rw [hN, hsum, hreal, Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]

end GlobalTheory.EisPerB


open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent in
theorem GlobalTheory.EisPerB.lattice_sum_eq_cone_sum : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F], GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz →
    ∀ (𝔞 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (k : ℕ), 2 ≤ k → Even k → ∀ (b : F), b ≠ 0 →
    ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F,
      Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) ∧
      HasSum (fun a : (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 : Set F) => GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm k 0 z ((a : F), b))
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ k / (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.cK F k : ℂ) *
          ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qTerm 𝔞 k z (ν.1, b)) := by
  intro F _ _ _ hLip 𝔞 k hk2 hke b hb z hz
  have hz'im : ∀ τ, ((fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) τ).im ≠ 0 := by
    intro τ
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  obtain ⟨hL, hR, hEq⟩ := hLip F (latM 𝔞) (GlobalTheory.EisPerB.latM_ne_zero 𝔞) k hk2 hke _ hz'im
  let e : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ≃ GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b :=
    Equiv.subtypeEquivRight (fun ν => GlobalTheory.T.mem_traceDualSignedPositiveCone_iff_totallyPositive F 𝔞 b hb z hz ν)
  have hN : (nrm 𝔞 : ℂ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (GlobalTheory.EisPerB.nrm_pos 𝔞).ne')
  have hRq : ∀ ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ),
      rhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ν = (nrm 𝔞 : ℂ) ^ (k - 1) * qTerm 𝔞 k z ((e ν).1, b) :=
    fun ν => GlobalTheory.EisPerB.rhsTerm_eq 𝔞 k z ν.1 b
  have hsumQ : Summable (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => qTerm 𝔞 k z (ν.1, b)) := by
    have h1 : Summable (fun ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) =>
        qTerm 𝔞 k z ((e ν).1, b)) := by
      refine (hR.mul_left ((nrm 𝔞 : ℂ) ^ (k - 1))⁻¹).congr fun ν => ?_
      rw [hRq, inv_mul_cancel_left₀ hN]
    exact e.summable_iff.1 h1
  have htsum : ∑' ν : dualCone (latM 𝔞) (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ),
      rhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) ν =
      (nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b) := by
    rw [tsum_congr hRq, tsum_mul_left]
    congr 1
    exact e.tsum_eq (fun ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b => qTerm 𝔞 k z (ν.1, b))
  refine ⟨hsumQ, ?_⟩
  have hE : (fun a : (latM 𝔞 : Set F) => eisTerm k 0 z ((a : F), b)) = fun a : (latM 𝔞 : Set F) =>
      ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
        lhsTerm k (fun τ : F →+* ℝ => ((τ b : ℝ) : ℂ) * z τ) a :=
    funext fun a => GlobalTheory.EisPerB.eisTerm_eq k z a b
  rw [hE]
  have h := hL.hasSum.mul_left ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹
  rw [hEq, htsum] at h
  rw [← GlobalTheory.T.lipschitzConstant_inverseDifferent_eisenstein F 𝔞 k (by omega)]
  have hv : ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ * lipConst k (latM 𝔞) *
      (nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b) =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ (k * Module.finrank ℚ F))⁻¹ *
      (lipConst k (latM 𝔞) * ((nrm 𝔞 : ℂ) ^ (k - 1) * ∑' ν : GlobalTheory.SlopeTestRemainingChoices.EisFibre.posCone 𝔞 b, qTerm 𝔞 k z (ν.1, b))) := by
    ring
  rw [hv]
  exact h
end
end
end
