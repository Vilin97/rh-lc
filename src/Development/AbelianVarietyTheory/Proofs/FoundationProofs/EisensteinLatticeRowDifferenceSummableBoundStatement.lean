module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FirstDiff

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.TermDiff

lemma rpow_neg_sub_le {x y p : ℝ} (hx : 1/2 ≤ x) (hxy : x ≤ y) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    |x ^ (-p) - y ^ (-p)| ≤ 8 * (y - x) / y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  set r := x / y with hr
  have hr0 : 0 < r := div_pos hx0 hy0
  have hr1 : r ≤ 1 := (div_le_one hy0).2 hxy
  have hyr : y ^ (-p) = x ^ (-p) * r ^ p := by
    rw [hr, Real.div_rpow hx0.le hy0.le, Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
    have : 0 < x ^ p := Real.rpow_pos_of_pos hx0 p
    have : 0 < y ^ p := Real.rpow_pos_of_pos hy0 p
    field_simp
  have hrp1 : r ^ p ≤ 1 := Real.rpow_le_one hr0.le hr1 hp0
  have hrp2 : r ^ (2:ℝ) ≤ r ^ p := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hp2
  have hr2 : r ^ (2:ℝ) = r ^ 2 := Real.rpow_two r
  have hxp : x ^ (-p) ≤ 4 := by
    rw [Real.rpow_neg hx0.le, ← Real.inv_rpow hx0.le]
    have h1 : x⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hx0 (by norm_num)]; linarith
    calc x⁻¹ ^ p ≤ (2:ℝ) ^ p := Real.rpow_le_rpow (inv_nonneg.2 hx0.le) h1 hp0
      _ ≤ (2:ℝ) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 4 := by norm_num
  have hxp0 : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx0.le _
  rw [hyr]
  have e : x ^ (-p) - x ^ (-p) * r ^ p = x ^ (-p) * (1 - r ^ p) := by ring
  rw [e, abs_of_nonneg (mul_nonneg hxp0 (by linarith))]
  have h1r : 1 - r ^ p ≤ 2 * (1 - r) := by
    have : 1 - r^2 ≤ 2 * (1 - r) := by nlinarith [mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hr1)]
    rw [hr2] at hrp2
    linarith
  have h1r' : 1 - r = (y - x) / y := by rw [hr]; field_simp
  calc x ^ (-p) * (1 - r ^ p) ≤ 4 * (2 * (1 - r)) :=
        mul_le_mul hxp h1r (by linarith) (by norm_num)
    _ = 8 * (y - x) / y := by rw [h1r']; ring

lemma norm_pow_sub_pow_le (z w : ℂ) (n : ℕ) (M : ℝ) (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖w ^ (n+1) - z ^ (n+1)‖ ≤ (n+1) * M ^ n * ‖w - z‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  have hM : 0 ≤ M := (norm_nonneg z).trans hz
  calc ‖∑ i ∈ Finset.range (n+1), w ^ i * z ^ (n + 1 - 1 - i)‖
      ≤ ∑ i ∈ Finset.range (n+1), ‖w ^ i * z ^ (n + 1 - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), M ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖w‖ ^ i * ‖z‖ ^ (n + 1 - 1 - i) ≤ M ^ i * M ^ (n + 1 - 1 - i) := by gcongr
          _ = M ^ n := by rw [← pow_add]; congr 1; omega
    _ = (n+1) * M ^ n := by simp

lemma inv_pow_sub_le (j : ℕ) (z w : ℂ) (hz : 0 < ‖z‖) (hwz : ‖w - z‖ ≤ ‖z‖ / 2) :
    ‖(z ^ j)⁻¹ - (w ^ j)⁻¹‖ ≤ j * 4 ^ j * ‖w - z‖ / ‖z‖ ^ (j + 1) := by
  have hW1 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
    have := norm_sub_le w (w - z); simpa using this
  have hW2 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
    have := norm_add_le z (w - z); simpa using this
  have hWl : ‖z‖ / 2 ≤ ‖w‖ := by linarith
  have hW0 : 0 < ‖w‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz
  have hw0 : w ≠ 0 := norm_pos_iff.1 hW0
  cases j with
  | zero => simp
  | succ n =>
    rw [inv_sub_inv (pow_ne_zero _ hz0) (pow_ne_zero _ hw0), norm_div, norm_mul, norm_pow, norm_pow]
    have hM : ‖w‖ ≤ 2 * ‖z‖ := by linarith
    have hnum := norm_pow_sub_pow_le z w n (2 * ‖z‖) (by linarith) hM
    have hden : ‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1) ≤ ‖z‖ ^ (n+1) * ‖w‖ ^ (n+1) := by gcongr
    have hdpos : 0 < ‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1) := by positivity
    calc ‖w ^ (n+1) - z ^ (n+1)‖ / (‖z‖ ^ (n+1) * ‖w‖ ^ (n+1))
        ≤ ((n+1) * (2 * ‖z‖) ^ n * ‖w - z‖) / (‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1)) :=
          div_le_div₀ (by positivity) hnum hdpos hden
      _ = (n+1) * 2 ^ (2 * n + 1) * ‖w - z‖ / ‖z‖ ^ (n + 2) := by
          rw [div_pow, mul_pow]; field_simp; ring
      _ ≤ ((n+1 : ℕ) : ℝ) * 4 ^ (n+1) * ‖w - z‖ / ‖z‖ ^ (n + 1 + 1) := by
          push_cast
          gcongr
          calc (2:ℝ) ^ (2 * n + 1) ≤ 2 ^ (2 * n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 4 ^ (n+1) := by rw [show 2 * n + 2 = 2 * (n+1) by ring, pow_mul]; norm_num

theorem first_diff : ∀ j : ℕ, ∃ C : ℝ, ∀ (s : ℝ) (z a : ℂ), 0 ≤ s → s ≤ 1 → 1 ≤ ‖z‖ → 2 * ‖a‖ ≤ ‖z‖ → ‖trm j s z - trm j s (z + a)‖ ≤ C * ‖a‖ / ‖z‖ ^ (j + 1) := by
  intro j
  refine ⟨j * 4 ^ j + 8 * 2 ^ j, ?_⟩
  intro s z a hs0 hs1 hz ha
  have hZ : 0 < ‖z‖ := by linarith
  have hwz : (z + a) - z = a := by ring
  have hA : ‖(z + a) - z‖ ≤ ‖z‖ / 2 := by rw [hwz]; linarith
  have hW1 : ‖z‖ ≤ ‖z + a‖ + ‖a‖ := by
    have := norm_sub_le (z + a) a; simpa using this
  have hW2 : ‖z + a‖ ≤ ‖z‖ + ‖a‖ := norm_add_le z a
  have hWl : ‖z‖ / 2 ≤ ‖z + a‖ := by linarith
  have hW0 : 0 < ‖z + a‖ := by linarith
  have hv : ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
  have hdv : ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)‖ ≤ 8 * ‖a‖ / ‖z‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, neg_mul]
    rcases le_total ‖z‖ ‖z + a‖ with h | h
    · refine (rpow_neg_sub_le (by linarith) h (by linarith) (by linarith)).trans ?_
      rw [div_le_div_iff₀ hW0 hZ]
      nlinarith
    · rw [abs_sub_comm]
      refine (rpow_neg_sub_le (by linarith) h (by linarith) (by linarith)).trans ?_
      gcongr
      linarith
  have hu' : ‖((z + a) ^ j)⁻¹‖ ≤ 2 ^ j / ‖z‖ ^ j := by
    rw [norm_inv, norm_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 1 * ‖z‖ ^ j = 2 ^ j * (‖z‖ / 2) ^ j := by rw [div_pow]; field_simp
      _ ≤ 2 ^ j * ‖z + a‖ ^ j := by gcongr
  have hdu := inv_pow_sub_le j z (z + a) hZ hA
  rw [hwz] at hdu
  unfold trm
  have e : (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((z + a) ^ j)⁻¹ * ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)
      = ((z ^ j)⁻¹ - ((z + a) ^ j)⁻¹) * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)
        + ((z + a) ^ j)⁻¹ * (((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)) := by ring
  rw [e]
  calc _ ≤ ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹‖ * ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ)‖
        + ‖((z + a) ^ j)⁻¹‖ * ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)‖ :=
          norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (j * 4 ^ j * ‖a‖ / ‖z‖ ^ (j + 1)) * 1 + (2 ^ j / ‖z‖ ^ j) * (8 * ‖a‖ / ‖z‖) := by
          gcongr
    _ = (j * 4 ^ j + 8 * 2 ^ j) * ‖a‖ / ‖z‖ ^ (j + 1) := by
          field_simp; ring

end GlobalTheory.EisM.TermDiff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FirstDiffStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.norm_trm_sub_trm_add_le : ∀ j : ℕ, ∃ C : ℝ, ∀ (s : ℝ) (z a : ℂ), 0 ≤ s → s ≤ 1 → 1 ≤ ‖z‖ → 2 * ‖a‖ ≤ ‖z‖ → ‖trm j s z - trm j s (z + a)‖ ≤ C * ‖a‖ / ‖z‖ ^ (j + 1) := by
  first | exact @GlobalTheory.EisM.TermDiff.first_diff | exact GlobalTheory.EisM.TermDiff.first_diff | (intros; apply GlobalTheory.EisM.TermDiff.first_diff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBound

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.RowBd

lemma summ3 : Summable (fun x : ℤ × ℤ => ‖x‖ ^ (-(3:ℝ))) := by
  have h := EisensteinSeries.summable_one_div_norm_rpow (k := 3) (by norm_num)
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h
  refine h.congr fun p => ?_
  simp [EisensteinSeries.norm_eq_max_natAbs, Prod.norm_def, Int.norm_eq_abs]

def shear (n : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (x.1, x.2 + n * x.1)
  invFun x := (x.1, x.2 - n * x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

lemma low (τ : ℍ) (c d : ℤ) :
    min 1 τ.im * ‖shear ⌊τ.re⌋ (c, d)‖ ≤ 2 * ‖(c : ℂ) * τ + d‖ := by
  set m := min 1 τ.im
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmy : m ≤ τ.im := min_le_right _ _
  have hm0 : 0 < m := lt_min one_pos τ.im_pos
  set z : ℂ := (c : ℂ) * τ + d
  have hre : z.re = c * τ.re + d := by simp [z]
  have him : z.im = c * τ.im := by simp [z]
  have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hfl0 : (0:ℝ) ≤ τ.re - ⌊τ.re⌋ := by have := Int.floor_le τ.re; linarith
  have hfl1 : τ.re - ⌊τ.re⌋ < 1 := by have := Int.lt_floor_add_one τ.re; linarith
  have hc : m * |(c:ℝ)| ≤ ‖z‖ := by
    rw [him, abs_mul, abs_of_pos τ.im_pos] at h2
    nlinarith [abs_nonneg (c:ℝ)]
  have he : |((d + ⌊τ.re⌋ * c : ℤ) : ℝ)| ≤ |z.re| + |(c:ℝ)| := by
    have : ((d + ⌊τ.re⌋ * c : ℤ) : ℝ) = z.re - c * (τ.re - ⌊τ.re⌋) := by rw [hre]; push_cast; ring
    rw [this]
    have ha := abs_sub z.re (c * (τ.re - ⌊τ.re⌋))
    have hb : |(c:ℝ) * (τ.re - ⌊τ.re⌋)| ≤ |(c:ℝ)| := by
      rw [abs_mul, abs_of_nonneg hfl0]
      nlinarith [abs_nonneg (c:ℝ)]
    linarith
  simp only [shear, Equiv.coe_fn_mk, Prod.norm_def, Int.norm_eq_abs]
  rw [mul_max_of_nonneg _ _ hm0.le, max_le_iff]
  constructor
  · nlinarith [norm_nonneg z]
  · nlinarith [abs_nonneg (c:ℝ), abs_nonneg z.re]

lemma trm_le {j : ℕ} (hj : 1 ≤ j) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ1 : μ ≤ 1) {z : ℂ} (hz : z = 0 ∨ μ ≤ ‖z‖) : ‖trm j s z‖ ≤ (μ ^ (j + 2))⁻¹ := by
  have hB : 1 ≤ (μ ^ (j + 2))⁻¹ := (one_le_inv₀ (pow_pos hμ0 _)).mpr (pow_le_one₀ hμ0.le hμ1)
  rcases hz with rfl | hz
  · simp [trm, zero_pow (by omega : j ≠ 0)]
    positivity
  set t := ‖z‖ with ht
  have ht0 : 0 < t := hμ0.trans_le hz
  have hn : ‖trm j s z‖ = (t ^ j)⁻¹ * t ^ (-2 * s) := by
    simp only [trm, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), ht]
  rw [hn]
  rcases le_or_gt 1 t with h1 | h1
  · have a1 : t ^ (-2 * s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have a2 : (t ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    have a3 : 0 ≤ t ^ (-2 * s) := Real.rpow_nonneg ht0.le _
    calc (t ^ j)⁻¹ * t ^ (-2 * s) ≤ 1 * 1 := mul_le_mul a2 a1 a3 zero_le_one
      _ ≤ _ := by linarith
  · have a1 : t ^ (-2 * s) ≤ t ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 h1.le (by linarith)
    have a3 : t ^ (-2:ℝ) = (t ^ 2)⁻¹ := by rw [Real.rpow_neg ht0.le]; norm_cast
    have a4 : 0 ≤ (t ^ j)⁻¹ := by positivity
    calc (t ^ j)⁻¹ * t ^ (-2 * s) ≤ (t ^ j)⁻¹ * (t ^ 2)⁻¹ := by
          rw [← a3]; exact mul_le_mul_of_nonneg_left a1 a4
      _ = (t ^ (j + 2))⁻¹ := by rw [pow_add, mul_inv]
      _ ≤ (μ ^ (j + 2))⁻¹ := inv_anti₀ (pow_pos hμ0 _) (pow_le_pow_left₀ hμ0.le hz _)

lemma dif_eq {L : ℕ} (hL : 0 < L) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    dif L v F x = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, (F x - F (x + (r:ℤ) • v)) := by
  simp only [dif]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub,
    ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hL.ne'), one_mul]

lemma dif_le {L : ℕ} (hL : 0 < L) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (x : ℤ × ℤ) (B : ℝ)
    (h : ∀ r ∈ Finset.range L, ‖F x - F (x + (r:ℤ) • v)‖ ≤ B) : ‖dif L v F x‖ ≤ B := by
  rw [dif_eq hL, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := norm_sum_le (Finset.range L) (fun r => F x - F (x + (r:ℤ) • v))
  have h2 : ∑ r ∈ Finset.range L, ‖F x - F (x + (r:ℤ) • v)‖ ≤ L * B := by
    simpa using Finset.sum_le_card_nsmul _ _ _ h
  rw [inv_mul_le_iff₀ (by exact_mod_cast hL)]
  linarith

lemma one_le_norm {x : ℤ × ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  rw [Prod.norm_def, Int.norm_eq_abs, Int.norm_eq_abs]
  by_cases h1 : x.1 = 0
  · have h2 : x.2 ≠ 0 := fun h => hx (Prod.ext h1 h)
    exact le_max_of_le_right (by exact_mod_cast Int.one_le_abs h2)
  · exact le_max_of_le_left (by exact_mod_cast Int.one_le_abs h1)

def g (x : ℤ × ℤ) : ℝ := ‖x‖ ^ (-(3:ℝ)) + if x = 0 then 1 else 0

lemma g_summ : Summable g := summ3.add (hasSum_ite_eq (0 : ℤ × ℤ) (1:ℝ)).summable

lemma g_nonneg (x : ℤ × ℤ) : 0 ≤ g x := by
  unfold g; have := Real.rpow_nonneg (norm_nonneg x) (-(3:ℝ)); split_ifs <;> linarith

lemma g_zero : g 0 = 1 := by simp [g, Real.zero_rpow (by norm_num : -(3:ℝ) ≠ 0)]

lemma g_ne {x : ℤ × ℤ} (hx : x ≠ 0) : g x = (‖x‖ ^ 3)⁻¹ := by
  simp only [g, if_neg hx, add_zero]
  rw [Real.rpow_neg (norm_nonneg x)]; norm_cast

theorem rowbd : ∀ j L : ℕ, 2 ≤ j → 0 < L → ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ∃ u : ℤ × ℤ → ℝ,
    Summable u ∧ ∑' x, u x ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧
    ∀ (s : ℝ) (x : ℤ × ℤ), 0 ≤ s → s ≤ 1 →
      ‖dif L (0, 1) (fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ u x := by
  intro j L hj hL
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.norm_trm_sub_trm_add_le j
  set C1' := max C1 0 with hC1'
  have hC1'0 : 0 ≤ C1' := le_max_right _ _
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL
  set K : ℝ := 2 ^ (j + 3) * (4 * L) ^ 3 + 8 * C1' * L with hK
  have hK0 : 0 ≤ K := by positivity
  set S : ℝ := ∑' x : ℤ × ℤ, g x
  have hS : 0 ≤ S := tsum_nonneg g_nonneg
  refine ⟨K * S, j + 5, fun τ => ?_⟩
  set m := min 1 τ.im with hmdef
  have hm0 : 0 < m := lt_min one_pos τ.im_pos
  have hm1 : m ≤ 1 := min_le_left _ _
  set e := shear ⌊τ.re⌋ with he
  set M : ℝ := (m ^ (j + 5))⁻¹ with hM
  refine ⟨fun x => K * M * g (e x), ?_, ?_, ?_⟩
  · exact (e.summable_iff.mpr g_summ).mul_left _
  · rw [tsum_mul_left, e.tsum_eq g]
    have hMb : M ≤ τ.im ^ (j + 5) + (τ.im ^ (j + 5))⁻¹ := by
      rcases le_total 1 τ.im with h | h
      · have h' : m = 1 := min_eq_left h
        have := one_le_pow₀ h (n := j + 5)
        have : 0 ≤ (τ.im ^ (j + 5))⁻¹ := by positivity
        rw [hM, h', one_pow, inv_one]; linarith
      · have h' : m = τ.im := min_eq_right h
        have := pow_pos τ.im_pos (j + 5)
        rw [hM, h']; linarith
    calc K * M * S = K * S * M := by ring
      _ ≤ K * S * (τ.im ^ (j + 5) + (τ.im ^ (j + 5))⁻¹) :=
        mul_le_mul_of_nonneg_left hMb (mul_nonneg hK0 hS)
  · intro s x hs0 hs1
    set F : ℤ × ℤ → ℂ := fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2) with hF
    have hlow : ∀ y : ℤ × ℤ, m * ‖e y‖ ≤ 2 * ‖(y.1 : ℂ) * τ + y.2‖ := fun y => low τ y.1 y.2
    have hez : ∀ y : ℤ × ℤ, e y = 0 → y = 0 := fun y hy => by
      simp only [he, shear, Equiv.coe_fn_mk, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hy ⊢
      obtain ⟨h1, h2⟩ := hy
      rw [h1, mul_zero, add_zero] at h2
      exact ⟨h1, h2⟩

    have hFb : ∀ y, ‖F y‖ ≤ ((m / 2) ^ (j + 2))⁻¹ := by
      intro y
      refine trm_le (by omega) hs0 hs1 (by positivity) (by linarith) ?_
      by_cases hy : y = 0
      · left; simp [hy]
      · right
        have h1 : 1 ≤ ‖e y‖ := one_le_norm (fun h => hy (hez y h))
        have := hlow y
        nlinarith
    have htr : ∀ r : ℕ, F (x + (r:ℤ) • ((0:ℤ), (1:ℤ))) =
        trm j s (((x.1 : ℂ) * τ + x.2) + (r:ℂ)) := by
      intro r; simp only [hF]; congr 1; simp; push_cast; ring
    have hM' : M = (m ^ (j + 2))⁻¹ * (m ^ 3)⁻¹ := by
      rw [hM, ← mul_inv, ← pow_add]
    have hm3 : 1 ≤ (m ^ 3)⁻¹ := (one_le_inv₀ (pow_pos hm0 _)).mpr (pow_le_one₀ hm0.le hm1)
    have ha0 : 0 < (m ^ (j + 2))⁻¹ := by positivity
    have hB0 : ((m / 2) ^ (j + 2))⁻¹ = 2 ^ (j + 2) * (m ^ (j + 2))⁻¹ := by
      rw [div_pow, inv_div, div_eq_mul_inv]
    set t := ‖(x.1 : ℂ) * τ + x.2‖ with ht
    set P := ‖e x‖ with hP
    have hxl : m * P ≤ 2 * t := hlow x
    have hP0 : 0 ≤ P := norm_nonneg _
    rcases le_or_gt (2 * (L:ℝ)) t with hA | hB
    ·
      have ht1 : 1 ≤ t := by linarith
      have ht0 : 0 < t := by linarith
      have hx0 : e x ≠ 0 := by
        intro h0
        have hx : x = 0 := hez x h0
        simp [ht, hx] at hA
        linarith
      have hP1 : 1 ≤ P := one_le_norm hx0
      have hstep : ∀ r ∈ Finset.range L, ‖F x - F (x + (r:ℤ) • ((0:ℤ), (1:ℤ)))‖ ≤
          C1' * L * (t ^ 3)⁻¹ := by
        intro r hr
        have hrL : (r:ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hr).le
        have hx' : F x = trm j s ((x.1 : ℂ) * τ + x.2) := rfl
        rw [htr, hx']
        have hra : ‖(r:ℂ)‖ = r := by simp
        have h := hC1 s ((x.1 : ℂ) * τ + x.2) (r:ℂ) hs0 hs1 ht1 (by rw [hra]; linarith)
        rw [hra, ← ht] at h
        have hpow : t ^ 3 ≤ t ^ (j + 1) := pow_le_pow_right₀ ht1 (by omega)
        have hr0 : (0:ℝ) ≤ r := by positivity
        calc _ ≤ C1 * r / t ^ (j + 1) := h
          _ ≤ C1' * r / t ^ (j + 1) := by gcongr; exact le_max_left _ _
          _ ≤ C1' * L / t ^ (j + 1) := by gcongr
          _ ≤ C1' * L / t ^ 3 := by gcongr
          _ = C1' * L * (t ^ 3)⁻¹ := by rw [div_eq_mul_inv]
      refine (dif_le hL _ F x _ hstep).trans ?_
      show C1' * L * (t ^ 3)⁻¹ ≤ K * M * g (e x)
      rw [g_ne hx0, hM']
      have hmP : 0 < m * P := by positivity
      have h8 : (t ^ 3)⁻¹ ≤ 8 * ((m * P) ^ 3)⁻¹ := by
        have h1 : (m * P) ^ 3 ≤ (2 * t) ^ 3 := pow_le_pow_left₀ hmP.le hxl 3
        have h2 : ((2 * t) ^ 3)⁻¹ ≤ ((m * P) ^ 3)⁻¹ := inv_anti₀ (by positivity) h1
        rw [mul_pow, mul_inv] at h2
        norm_num at h2
        linarith
      have hmp : ((m * P) ^ 3)⁻¹ = (m ^ 3)⁻¹ * (P ^ 3)⁻¹ := by rw [mul_pow, mul_inv]
      have hq0 : 0 ≤ (m ^ 3)⁻¹ * (P ^ 3)⁻¹ := by positivity
      have hK1 : 8 * C1' * L ≤ K := by
        have : (0:ℝ) ≤ 2 ^ (j + 3) * (4 * L) ^ 3 := by positivity
        rw [hK]; linarith
      calc C1' * L * (t ^ 3)⁻¹ ≤ C1' * L * (8 * ((m ^ 3)⁻¹ * (P ^ 3)⁻¹)) := by
            rw [← hmp]; exact mul_le_mul_of_nonneg_left h8 (by positivity)
        _ = (8 * C1' * L) * 1 * ((m ^ 3)⁻¹ * (P ^ 3)⁻¹) := by ring
        _ ≤ K * (m ^ (j + 2))⁻¹ * ((m ^ 3)⁻¹ * (P ^ 3)⁻¹) := by
            gcongr
            exact (one_le_inv₀ (pow_pos hm0 _)).mpr (pow_le_one₀ hm0.le hm1)
        _ = K * ((m ^ (j + 2))⁻¹ * (m ^ 3)⁻¹) * (P ^ 3)⁻¹ := by ring
    ·
      have hstep : ∀ r ∈ Finset.range L, ‖F x - F (x + (r:ℤ) • ((0:ℤ), (1:ℤ)))‖ ≤
          2 * ((m / 2) ^ (j + 2))⁻¹ := by
        intro r _
        have h1 := hFb x
        have h2 := hFb (x + (r:ℤ) • ((0:ℤ), (1:ℤ)))
        exact (norm_sub_le _ _).trans (by linarith)
      refine (dif_le hL _ F x _ hstep).trans ?_
      show 2 * ((m / 2) ^ (j + 2))⁻¹ ≤ K * M * g (e x)
      rw [hB0, hM']
      have hK2 : 2 ^ (j + 3) * (4 * L) ^ 3 ≤ K := by
        have : 0 ≤ 8 * C1' * L := by positivity
        rw [hK]; linarith
      have h2j : (2:ℝ) * 2 ^ (j + 2) = 2 ^ (j + 3) := by ring
      by_cases hx0 : e x = 0
      · rw [hx0, g_zero]
        have h4 : (1:ℝ) ≤ (4 * L) ^ 3 := one_le_pow₀ (by linarith)
        have hK3 : 2 ^ (j + 3) ≤ K := by
          have : (2:ℝ) ^ (j + 3) * 1 ≤ 2 ^ (j + 3) * (4 * L) ^ 3 := by gcongr
          linarith
        calc 2 * (2 ^ (j + 2) * (m ^ (j + 2))⁻¹) = 2 ^ (j + 3) * (m ^ (j + 2))⁻¹ * 1 := by
              rw [← h2j]; ring
          _ ≤ K * (m ^ (j + 2))⁻¹ * (m ^ 3)⁻¹ := by gcongr
          _ = _ := by ring
      · rw [g_ne hx0]
        have hP1 : 1 ≤ P := one_le_norm hx0
        have hmP : 0 < m * P := by positivity
        have hmPL : (m * P) ^ 3 ≤ (4 * L) ^ 3 := pow_le_pow_left₀ hmP.le (by linarith) 3
        have hinv : ((4 * (L:ℝ)) ^ 3)⁻¹ ≤ (m ^ 3)⁻¹ * (P ^ 3)⁻¹ := by
          rw [← mul_inv, ← mul_pow]; exact inv_anti₀ (by positivity) hmPL
        have h4 : (0:ℝ) < (4 * L) ^ 3 := by positivity
        calc 2 * (2 ^ (j + 2) * (m ^ (j + 2))⁻¹)
            = 2 ^ (j + 3) * (4 * L) ^ 3 * (m ^ (j + 2))⁻¹ * ((4 * (L:ℝ)) ^ 3)⁻¹ := by
              rw [← h2j]; field_simp
          _ ≤ K * (m ^ (j + 2))⁻¹ * ((m ^ 3)⁻¹ * (P ^ 3)⁻¹) := by gcongr
          _ = K * ((m ^ (j + 2))⁻¹ * (m ^ 3)⁻¹) * (P ^ 3)⁻¹ := by ring

end GlobalTheory.RowBd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBoundStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound : ∀ j L : ℕ, 2 ≤ j → 0 < L → ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ∃ u : ℤ × ℤ → ℝ, Summable u ∧ ∑' x, u x ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧ ∀ (s : ℝ) (x : ℤ × ℤ), 0 ≤ s → s ≤ 1 → ‖dif L (0, 1) (fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ u x := by
  first | exact @GlobalTheory.RowBd.rowbd | exact GlobalTheory.RowBd.rowbd | (intros; apply GlobalTheory.RowBd.rowbd <;> assumption)
end
end
