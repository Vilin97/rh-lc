module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumReindexNat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCommonDenominatorEqMonomialMulPowerSerStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumPowerSeriesInvOfConvergentStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperationsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicPropertiesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumNeZero

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_hsne_re (N : ℕ) (z : ℂ) :
    (2 * Real.pi * Complex.I * z / N).re = -(2 * Real.pi * z.im / N) := by
  have : (2 * Real.pi * Complex.I * z / N) = ((2 * Real.pi / N : ℝ) : ℂ) * (Complex.I * z) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  simp [Complex.mul_re]
  ring

theorem fn_hsne_pre (N : ℕ) (hN : 0 < N) (C : ℝ) (x : ℂ) (hx : x ≠ 0)
    (hxr : ‖x‖ < Real.exp (-(2 * Real.pi * C / N))) :
    ∃ z : ℂ, C < z.im ∧ Complex.exp (2 * Real.pi * Complex.I * z / N) = x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi), ?_, ?_⟩
  · have hlog : Real.log ‖x‖ < -(2 * Real.pi * C / N) := by
      rw [Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hx)]; exact hxr
    have him : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)).im
        = -(N * Real.log ‖x‖) / (2 * Real.pi) := by
      have : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi))
          = ((-(N : ℝ) / (2 * Real.pi) : ℝ) : ℂ) * (Complex.I * Complex.log x) := by
        push_cast; ring
      rw [this, Complex.im_ofReal_mul]
      simp [Complex.mul_im, Complex.log_re]
      ring
    rw [him]
    rw [lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hlog hNr
    have e : (N : ℝ) * -(2 * Real.pi * C / N) = -(C * (2 * Real.pi)) := by
      field_simp
    nlinarith [this, e]
  · have : 2 * Real.pi * Complex.I * (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)) / N
        = Complex.log x := by
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      field_simp
      ring_nf
      rw [Complex.I_sq]; ring
    rw [this, Complex.exp_log hx]

end GlobalTheory

namespace GlobalTheory

theorem fn_hasSum_ne_zero : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω),
    Den h → h ≠ 0 → HS ε C φ h → ∃ C' : ℝ, ∀ z : ℂ, C' < z.im → φ z ≠ 0 := by
  intro Ω _ ε C φ h hD h0 hS
  obtain ⟨N, n₀, a, hN, ha0, ha, hz⟩ := GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD h0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  set b : ℕ → ℂ := fun k => ε (a k) with hb
  have hb0 : b 0 ≠ 0 := by
    simp only [hb]; exact (map_ne_zero ε).mpr ha0

  have key : ∀ z : ℂ, C < z.im →
      HasSum (fun k : ℕ => b k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k)
        (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := fun z hzC =>
    (fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN ha hz).mp (hS z hzC)
  set ρ : ℝ := Real.exp (-(2 * Real.pi * C / N)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hsum : ∀ x : ℂ, ‖x‖ < ρ → Summable fun n => b n * x ^ n := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      have : n ≠ 0 := by simpa using hn
      simp [zero_pow this]
    · obtain ⟨z, hzC, hzx⟩ := fn_hsne_pre N hN C x hx0 hx
      have := key z hzC
      rw [hzx] at this
      exact this.summable
  obtain ⟨ρ', hρ'0, hρ'⟩ := GlobalTheory.T.hasSum_powerSeries_inv_of_convergent b ρ hρ0 hb0 hsum
  refine ⟨max C (-(N * Real.log ρ') / (2 * Real.pi)), fun z hzi => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hzi
  have hz2 : -(N * Real.log ρ') / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hzi
  set x := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hxn : ‖x‖ < ρ' := by
    rw [hxdef, Complex.norm_exp, fn_hsne_re]
    rw [← Real.exp_log hρ'0, Real.exp_lt_exp]
    rw [div_lt_iff₀ (by positivity)] at hz2
    rw [neg_lt, lt_div_iff₀ hNr]
    nlinarith [hz2]
  have hne := (hρ' x hxn).1
  rw [(key z hzC).tsum_eq] at hne
  intro hφ
  apply hne
  rw [hφ, zero_mul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumNeZeroStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_im_gt_ne_zero_of_hs : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → HS ε C φ h → ∃ C' : ℝ, ∀ z : ℂ, C' < z.im → φ z ≠ 0 := by
  first | exact @GlobalTheory.fn_hasSum_ne_zero | exact GlobalTheory.fn_hasSum_ne_zero | (intros; apply GlobalTheory.fn_hasSum_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEq

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hs_uniq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  intro Ω _ ε C C' C'' φ φ' h h' hd hd' hs hs' heq
  obtain ⟨hmono, hadd, -, hcongr⟩ := GlobalTheory.T.hasQExpansionSumAbove_basic_properties Ω ε
  set C₀ : ℝ := max C (max C' C'') with hC₀
  have h1 : HS ε C₀ φ h := hmono C C₀ φ h (le_max_left _ _) hs
  have h2 : HS ε C₀ φ' h' := hmono C' C₀ φ' h' (le_trans (le_max_left _ _) (le_max_right _ _)) hs'
  have h3 : HS ε C₀ (φ - φ') (h - h') := ((hadd C₀ φ φ' h h') h1 h2).2
  have h4 : HS ε C₀ (fun _ => (0 : ℂ)) (h - h') := by
    refine hcongr C₀ (φ - φ') (fun _ => 0) (h - h') ?_ h3
    intro z hz
    have : C'' < z.im := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hz
    simp [heq z this]
  have hdd : Den (h - h') := (((GlobalTheory.T.hasCommonExponentDenominator_ring_operations Ω).1 h h' hd hd').2.1)
  by_contra hne
  have hne' : h - h' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨D, hD⟩ := GlobalTheory.T.exists_im_gt_ne_zero_of_hs Ω ε C₀ (fun _ => (0 : ℂ)) (h - h') hdd hne' h4
  exact hD ((D + 1 : ℝ) * Complex.I) (by simp) rfl

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEqStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hahnSeries_eq_of_qExpansionSumAbove_eventually_eq : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C C' C'' : ℝ) (φ φ' : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), Den h → Den h' → HS ε C φ h → HS ε C' φ' h' → (∀ z : ℂ, C'' < z.im → φ z = φ' z) → h = h' := by
  first | exact @GlobalTheory.FN.hs_uniq | exact GlobalTheory.FN.hs_uniq | (intros; apply GlobalTheory.FN.hs_uniq <;> assumption)
end
end
