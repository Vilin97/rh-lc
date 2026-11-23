module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Trigonometric
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedFejerPositivity

section

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem normSq_geomSum_le_fejer (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    Complex.normSq (∑ j ∈ Finset.range (J + 1), w ^ j) ≤
      (J + 1 : ℝ) + 2 * ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re := by
  have hre : ∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), w ^ j).re
      = 1 + ∑ j ∈ Finset.Icc 1 n, (w ^ j).re := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Complex.add_re, ih, Finset.sum_Icc_succ_top (by omega)]
      ring
  induction J with
  | zero => simp
  | succ J ih =>
    have h1 : ∑ j ∈ Finset.range (J + 1 + 1), w ^ j
        = w * (∑ j ∈ Finset.range (J + 1), w ^ j) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp [pow_succ']
    have h2 : ∑ j ∈ Finset.Icc 1 (J + 1), (((J + 1 : ℕ) : ℝ) + 1 - j) * (w ^ j).re
        = ∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re
          + ∑ j ∈ Finset.Icc 1 (J + 1), (w ^ j).re := by
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ← add_assoc,
        ← Finset.sum_add_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; ring
      · push_cast; ring
    have h3 := hre (J + 1)
    have hw2 : Complex.normSq w ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      have := norm_nonneg w
      nlinarith
    rw [h2]
    set S := ∑ j ∈ Finset.range (J + 1), w ^ j
    rw [h1] at h3 ⊢
    have h4 : Complex.normSq (w * S + 1) = Complex.normSq w * Complex.normSq S
        + 2 * (w * S + 1).re - 1 := by
      rw [Complex.normSq_add, map_mul]
      simp
      ring
    have h5 := Complex.normSq_nonneg S
    rw [h4, h3]
    push_cast
    nlinarith

theorem fejer_re_ge (w : ℂ) (hw : ‖w‖ ≤ 1) (J : ℕ) :
    -(1 / 2) ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re := by
  have h := normSq_geomSum_le_fejer w hw J
  have h0 := Complex.normSq_nonneg (∑ j ∈ Finset.range (J + 1), w ^ j)
  have hJ : (0 : ℝ) < J + 1 := by positivity
  have h1 : ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
      = (∑ j ∈ Finset.Icc 1 J, ((J : ℝ) + 1 - j) * (w ^ j).re) / (J + 1) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [h1, le_div_iff₀ hJ]
  linarith

theorem sum_fejer_weights (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) = (J : ℝ) / 2 := by
  have h : ∀ n : ℕ, ∑ j ∈ Finset.Icc 1 n, (j : ℝ) = n * (n + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast; ring
  have hJ : (0 : ℝ) < J + 1 := by positivity
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, h]
  simp
  field_simp
  ring

theorem weighted_fejer_split (J : ℕ) (θ : ℝ) (w : ℂ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re
      = ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (θ * I)) ^ j).re) / 2
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1))
            * ((w * Complex.exp (-(θ * I))) ^ j).re) / 2 := by
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : Complex.exp (θ * I) ^ j = Complex.exp (((j * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Complex.exp (-(θ * I)) ^ j = Complex.exp (((-(j * θ) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, mul_pow, e1, e2, Complex.mul_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im,
    Real.cos_neg, Real.sin_neg]
  ring

theorem weighted_fejer_positivity : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  intro J θ
  have n1 : ‖Complex.exp (θ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have n2 : ‖Complex.exp (-(θ * I))‖ = 1 := by
    rw [Complex.exp_neg, norm_inv, n1, inv_one]
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [weighted_fejer_split]
    have a := fejer_re_ge w hw J
    have b := fejer_re_ge (w * Complex.exp (θ * I)) (by rw [norm_mul, n1, mul_one]; exact hw) J
    have c := fejer_re_ge (w * Complex.exp (-(θ * I)))
      (by rw [norm_mul, n2, mul_one]; exact hw) J
    linarith
  · rw [weighted_fejer_split]
    have a := fejer_re_ge (Complex.exp (θ * I)) n1.le J
    have b := fejer_re_ge (Complex.exp (θ * I) * Complex.exp (θ * I))
      (by rw [norm_mul, n1, mul_one]) J
    have c : Complex.exp (θ * I) * Complex.exp (-(θ * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [c]
    simp only [one_pow, Complex.one_re, mul_one]
    rw [sum_fejer_weights]
    linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedFejerPositivityStatement

section

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  first | exact @GlobalTheory.weighted_fejer_positivity | exact GlobalTheory.weighted_fejer_positivity | (intros; apply GlobalTheory.weighted_fejer_positivity <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumIccThreeQuartersPowLe

section

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem sum_Icc_three_quarters_pow_le (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 3 - 3 * (3 / 4 : ℝ) ^ J := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [pow_succ]
    linarith

theorem powerSum_weighted_ineq {ι : Type} (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι)
    (L δ x : ℝ) (hi : i₀ ∈ S) (hb : 1 ≤ b i₀) (hL : 1 ≤ L) (hδ : 0 < δ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) (hz : 1 / (1 + x) ≤ ‖z i₀‖) (hS : (∑ i ∈ S, (b i : ℝ)) ≤ L)
    (hp : ∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) (J : ℕ) :
    (J : ℝ) / 4 - 7 * L ≤ 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by
  classical
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image (S.filter fun i => 1 ≤ b i)
    (fun i => ‖z i‖) ⟨i₀, Finset.mem_filter.2 ⟨hi, hb⟩⟩
  obtain ⟨hi₁S, hb₁⟩ := Finset.mem_filter.1 hi₁
  set R : ℝ := ‖z i₁‖ with hR
  have h1x : 0 < 1 + x := by linarith
  have hRge : 1 / (1 + x) ≤ R := hz.trans (hmax i₀ (Finset.mem_filter.2 ⟨hi, hb⟩))
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRge
  have hRinv : R⁻¹ ≤ 1 + x := by
    rw [inv_le_comm₀ hRpos h1x, ← one_div]; exact hRge
  have hRinv0 : 0 ≤ R⁻¹ := by positivity
  set θ : ℝ := Complex.arg (z i₁) with hθ
  obtain ⟨hF1, hF2⟩ := GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound J θ
  set c : ℕ → ℝ := fun j => (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) with hc
  set F : ℂ → ℝ := fun w => ∑ j ∈ Finset.Icc 1 J, c j * (w ^ j).re with hF
  have hF1' : ∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ F w := hF1
  have hF2' : (J : ℝ) / 4 - 3 / 4 ≤ F (Complex.exp (θ * I)) := hF2
  set w : ι → ℂ := fun i => ((R⁻¹ : ℝ) : ℂ) * z i with hw
  have hw₁ : w i₁ = Complex.exp (θ * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (z i₁)
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    show ((R⁻¹ : ℝ) : ℂ) * z i₁ = _
    rw [← h]
    push_cast
    rw [← hR, ← hθ, ← mul_assoc, inv_mul_cancel₀ hR', one_mul]
  have hwn : ∀ i ∈ S, 1 ≤ b i → ‖w i‖ ≤ 1 := by
    intro i hiS hbi
    have := hmax i (Finset.mem_filter.2 ⟨hiS, hbi⟩)
    show ‖((R⁻¹ : ℝ) : ℂ) * z i‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hRinv0, inv_mul_le_iff₀ hRpos, mul_one]
    exact this

  have hlow : (J : ℝ) / 4 - L ≤ ∑ i ∈ S, (b i : ℝ) * F (w i) := by
    have hnn : ∀ i ∈ S, 0 ≤ (b i : ℝ) * (F (w i) + 1) := by
      intro i hiS
      rcases Nat.eq_zero_or_pos (b i) with h0 | h0
      · simp [h0]
      · have := hF1' _ (hwn i hiS h0)
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have h1 := Finset.single_le_sum hnn hi₁S
    have hb1 : (1 : ℝ) ≤ b i₁ := by exact_mod_cast hb₁
    have h2 := hF1' _ (hwn i₁ hi₁S hb₁)
    have h3 : F (w i₁) + 1 ≤ (b i₁ : ℝ) * (F (w i₁) + 1) := by nlinarith
    have h4 : ∑ i ∈ S, (b i : ℝ) * (F (w i) + 1)
        = ∑ i ∈ S, (b i : ℝ) * F (w i) + ∑ i ∈ S, (b i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [← hw₁] at hF2'
    linarith

  have hex : ∑ i ∈ S, (b i : ℝ) * F (w i)
      = ∑ j ∈ Finset.Icc 1 J, c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re) := by
    simp only [hF, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e1 : (w i ^ j).re = R⁻¹ ^ j * (z i ^ j).re := by
      show ((((R⁻¹ : ℝ) : ℂ) * z i) ^ j).re = _
      rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have e2 : ((b i : ℂ) * z i ^ j).re = (b i : ℝ) * (z i ^ j).re := by
      rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e1, e2]; ring

  have hup : ∀ j ∈ Finset.Icc 1 J,
      c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ 4 * J * δ * (1 + x) ^ J + 2 * L * (3 / 4 : ℝ) ^ j := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.1 hj
    have hjJ' : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hJ1 : (0 : ℝ) < J + 1 := by positivity
    have ha0 : 0 ≤ 1 - (j : ℝ) / (J + 1) := by
      rw [sub_nonneg, div_le_one hJ1]; linarith
    have ha1 : 1 - (j : ℝ) / (J + 1) ≤ 1 := by
      have : 0 ≤ (j : ℝ) / (J + 1) := by positivity
      linarith
    have hcos1 := Real.cos_le_one (j * θ)
    have hcos2 := Real.neg_one_le_cos (j * θ)
    have hc0 : 0 ≤ c j := mul_nonneg ha0 (by linarith)
    have hc2 : c j ≤ 2 := by
      show (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) ≤ 2
      nlinarith
    have hq : R⁻¹ ^ j ≤ (1 + x) ^ j := pow_le_pow_left₀ hRinv0 hRinv j
    have hq2 : (1 + x) ^ j ≤ (1 + x) ^ J := pow_le_pow_right₀ (by linarith) hjJ
    have hq3 : (1 + x) ^ j ≤ (3 / 2 : ℝ) ^ j := pow_le_pow_left₀ h1x.le (by linarith) j
    have hB0 : 0 ≤ 2 * j * δ + L / 2 ^ j := by positivity
    have s1 : R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re
        ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) :=
      (mul_le_mul_of_nonneg_left (hp j hj1) (by positivity)).trans
        (mul_le_mul_of_nonneg_right hq hB0)
    have s2 : (1 + x) ^ j * (2 * j * δ) ≤ (1 + x) ^ J * (2 * J * δ) := by gcongr
    have s3 : (1 + x) ^ j * (L / 2 ^ j) ≤ (3 / 2 : ℝ) ^ j * (L / 2 ^ j) := by gcongr
    have s4 : (3 / 2 : ℝ) ^ j * (L / 2 ^ j) = L * (3 / 4 : ℝ) ^ j := by
      have : (3 / 4 : ℝ) ^ j = (3 / 2 : ℝ) ^ j / 2 ^ j := by rw [← div_pow]; norm_num
      rw [this]; ring
    have s5 : 0 ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) := by positivity
    calc c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ c j * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_left s1 hc0
      _ ≤ 2 * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_right hc2 s5
      _ ≤ _ := by rw [mul_add ((1 + x) ^ j)]; linarith
  have hsum := Finset.sum_le_sum hup
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hg := sum_Icc_three_quarters_pow_le J
  have hg0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ J := by positivity
  have hg' : 2 * L * ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 2 * L * 3 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have : (J : ℝ) * (4 * J * δ * (1 + x) ^ J) = 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by ring
  linarith

theorem powerSum_repulsion :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι) (L δ x : ℝ), i₀ ∈ S → 1 ≤ b i₀ → 1 ≤ L → 0 < δ → 0 ≤ x → x ≤ 1 / 2 → 1 / (1 + x) ≤ ‖z i₀‖ → (∑ i ∈ S, (b i : ℝ)) ≤ L → (∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) → Real.log (1 / (C * L * δ)) / (C * L) ≤ x := by
  refine ⟨2080, by norm_num, ?_⟩
  intro ι S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp
  have h := powerSum_weighted_ineq S z b i₀ L δ x hi hb hL hδ hx0 hx hz hS hp ⌈64 * L⌉₊
  set J : ℕ := ⌈64 * L⌉₊ with hJ
  have hJ1 : 64 * L ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) ≤ 65 * L := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 64 * L by linarith)
    linarith
  have hJ0 : (0 : ℝ) < J := by linarith
  have hP : (1 + x) ^ J ≤ Real.exp (x * J) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) J
  have hP0 : 0 < (1 + x) ^ J := by positivity
  have h1 : (J : ℝ) * 1 ≤ J * (32 * J * δ * (1 + x) ^ J) := by nlinarith
  have h2 : 1 ≤ 32 * J * δ * (1 + x) ^ J := le_of_mul_le_mul_left h1 hJ0
  have h3 : 32 * J * δ * (1 + x) ^ J ≤ 2080 * L * δ * Real.exp (x * J) := by
    have : 32 * (J : ℝ) ≤ 2080 * L := by linarith
    gcongr
  have hD : 0 < 2080 * L * δ := by positivity
  have h4 : 1 / (2080 * L * δ) ≤ Real.exp (x * J) := by
    rw [div_le_iff₀ hD]; linarith
  have h5 : Real.log (1 / (2080 * L * δ)) ≤ x * J :=
    (Real.log_le_iff_le_exp (by positivity)).2 h4
  rw [div_le_iff₀ (by positivity)]
  have : x * J ≤ x * (2080 * L) := mul_le_mul_of_nonneg_left (by linarith) hx0
  linarith

end GlobalTheory
end
end
