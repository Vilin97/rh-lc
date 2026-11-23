module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QFormCountStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassIdealCountEqNcardShiftedBinaryFormStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
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
public import Mathlib.NumberTheory.ZetaValues
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Separation.CompletelyRegular

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SummableExpNegMulSq

section

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ShiftedTheta

theorem hasSum_int_inv_sq :
    HasSum (fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 3) := by
  have h := HasSum.of_nat_of_neg (f := fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2)
    (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)
    (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)
  have e : Real.pi ^ 2 / 6 + Real.pi ^ 2 / 6 - 1 / ((0 : ℤ) : ℝ) ^ 2 = Real.pi ^ 2 / 3 := by
    simp
    ring
  exact e ▸ h

theorem exp_neg_le {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 2
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  norm_num [Nat.factorial] at h
  linarith

theorem exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-(c * (n : ℝ) ^ 2)) ≤ 2 / c ^ 2 * (1 / (n : ℝ) ^ 2) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by
      have := sq_pos_of_ne_zero hn
      omega
    exact_mod_cast this
  refine (exp_neg_le (by positivity)).trans ?_
  rw [div_mul_div_comm, mul_one, mul_pow]
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  nlinarith

theorem summable_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually (hasSum_int_inv_sq.summable.mul_left (2 / c ^ 2)) ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_mul_sq_le hc hn

theorem summable_shifted {s : ℝ} (θ : ℝ) (hs : 0 < s) :
    Summable fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
    ((summable_exp_neg_mul_sq (half_pos hs)).mul_left (Real.exp (s * θ ^ 2)))
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hs.le (sq_nonneg ((m : ℝ) + 2 * θ))]

theorem poisson {s : ℝ} (θ : ℝ) (hs : 0 < s) :
    ((∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) : ℝ) : ℂ) =
      (Real.sqrt (Real.pi / s) : ℂ) * ∑' n : ℤ,
        cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) := by
  have ha : 0 < Real.pi / s := div_pos Real.pi_pos hs
  rw [Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re])]
  have h1 : ((Real.pi / s : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / s) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow ha.le]
    norm_num
  have h2 : (Real.sqrt (Real.pi / s) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  rw [h1, ← mul_assoc, mul_one_div_cancel h2, one_mul, ofReal_tsum]
  refine tsum_congr fun n => ?_
  have h3 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h5 : I * (-I * θ) = θ := by
    rw [← mul_assoc, mul_neg, I_mul_I]; ring
  rw [h5]
  push_cast
  congr 1
  field_simp

theorem shifted_theta_bound : ∀ s θ : ℝ, 0 < s → Summable (fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2))) ∧ |∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) - Real.sqrt (Real.pi / s)| ≤ Real.sqrt (Real.pi / s) * s ^ 2 := by
  intro s θ hs
  refine ⟨summable_shifted θ hs, ?_⟩
  set g : ℤ → ℂ := fun n =>
    cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) with hg
  have hpi := Real.pi_pos
  have hc : 0 < Real.pi ^ 2 / s := by positivity
  have hn : ∀ n : ℤ, ‖g n‖ = Real.exp (-(Real.pi ^ 2 / s * (n : ℝ) ^ 2)) := by
    intro n
    have e : -(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n
        = ((-(Real.pi ^ 2 / s * (n : ℝ) ^ 2) : ℝ) : ℂ) + ((-(2 * Real.pi * θ * n) : ℝ) : ℂ) * I := by
      push_cast
      ring
    simp only [hg]
    rw [e, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_exp_ofReal]
  have hsum : Summable g :=
    Summable.of_norm_bounded (summable_exp_neg_mul_sq hc) fun n => (hn n).le
  have hb : ‖∑' n : ℤ, if n = 0 then 0 else g n‖ ≤ 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) := by
    refine tsum_of_norm_bounded (hasSum_int_inv_sq.mul_left _) fun n => ?_
    split_ifs with h
    · rw [norm_zero]; positivity
    · rw [hn]; exact exp_neg_mul_sq_le hc h
  have hb2 : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) ≤ s ^ 2 := by
    have e : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) = s ^ 2 * (2 / (3 * Real.pi ^ 2)) := by
      field_simp
    rw [e]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hg0 : g 0 = 1 := by simp [hg]
  have hp := poisson θ hs
  change _ = _ * ∑' n, g n at hp
  rw [hsum.tsum_eq_add_tsum_ite 0, hg0] at hp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ofReal_sub, hp, mul_add, mul_one,
    add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hb.trans hb2) (Real.sqrt_nonneg _)

end GlobalTheory.ShiftedTheta
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaQForm

section

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem tsum_prod_weight_approx {ι κ : Type} (u : ι → κ → ℝ) (w : κ → ℝ) (A a C c : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hu0 : ∀ m k, 0 ≤ u m k) (hw0 : ∀ k, 0 ≤ w k)
    (hu : ∀ k, Summable (fun m => u m k) ∧ |∑' m, u m k - A| ≤ A * a)
    (hw : Summable w ∧ |∑' k, w k - C| ≤ C * c) :
    Summable (fun v : ι × κ => u v.1 v.2 * w v.2) ∧
      |∑' v : ι × κ, u v.1 v.2 * w v.2 - A * C| ≤ A * C * (a + c + a * c) := by
  have hin : ∀ k, ∑' m, u m k * w k = (∑' m, u m k) * w k := fun k => tsum_mul_right
  have hb : ∀ k, ‖(∑' m, u m k - A) * w k‖ ≤ A * a * w k := fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 k)]
    exact mul_le_mul_of_nonneg_right (hu k).2 (hw0 k)
  have hs1 : Summable (fun k => (∑' m, u m k - A) * w k) :=
    Summable.of_norm_bounded (hw.1.mul_left (A * a)) hb
  have hs2 : Summable (fun k => (∑' m, u m k) * w k) := by
    refine (hs1.add (hw.1.mul_left A)).congr fun k => ?_
    ring
  have hsw : Summable (fun v : κ × ι => u v.2 v.1 * w v.1) := by
    rw [summable_prod_of_nonneg (fun v => mul_nonneg (hu0 _ _) (hw0 _))]
    refine ⟨fun k => ?_, ?_⟩
    · exact (hu k).1.mul_right (w k)
    · exact hs2.congr fun k => (hin k).symm
  have hs : Summable (fun v : ι × κ => u v.1 v.2 * w v.2) :=
    hsw.prod_symm
  refine ⟨hs, ?_⟩
  have h1 : ∑' v : ι × κ, u v.1 v.2 * w v.2 = ∑' k, (∑' m, u m k) * w k := by
    rw [← (Equiv.prodComm κ ι).tsum_eq]
    have := hsw.tsum_prod
    simp only [hin] at this
    exact this
  have h2 : ∑' k, (∑' m, u m k) * w k = ∑' k, (∑' m, u m k - A) * w k + A * ∑' k, w k := by
    rw [← tsum_mul_left, ← hs1.tsum_add (hw.1.mul_left A)]
    exact tsum_congr fun k => by ring
  have h3 : |∑' k, (∑' m, u m k - A) * w k| ≤ A * a * ∑' k, w k := by
    have := tsum_of_norm_bounded (hw.1.hasSum.mul_left (A * a)) hb
    simpa using this
  rw [h1, h2]
  have h4 := abs_le.mp hw.2
  have h5 := abs_le.mp h3
  have h6 : A * a * ∑' k, w k ≤ A * a * (C + C * c) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA ha)
  have h7 : A * (∑' k, w k - C) ≤ A * (C * c) := mul_le_mul_of_nonneg_left h4.2 hA
  have h8 : A * (-(C * c)) ≤ A * (∑' k, w k - C) := mul_le_mul_of_nonneg_left h4.1 hA
  rw [abs_le]
  constructor <;> nlinarith

theorem theta_qForm : ∀ α γ l θ₁ θ₂ t : ℝ, 0 < α → 0 < γ → 0 < t → Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧ |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) - Real.pi / Real.sqrt (α * γ) / t| ≤ Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2) := by
  intro α γ l θ₁ θ₂ t hα hγ ht
  have h := tsum_prod_weight_approx
    (fun (m : ℤ) (k : ℤ) => Real.exp (-((α * t) * (m + (θ₁ + l * k)) ^ 2)))
    (fun k : ℤ => Real.exp (-((γ * t) * (k + θ₂) ^ 2)))
    (Real.sqrt (Real.pi / (α * t))) ((α * t) ^ 2) (Real.sqrt (Real.pi / (γ * t))) ((γ * t) ^ 2)
    (Real.sqrt_nonneg _) (sq_nonneg _) (fun _ _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (fun k => GlobalTheory.ShiftedTheta.shifted_theta_bound (α * t) (θ₁ + l * k) (mul_pos hα ht))
    (GlobalTheory.ShiftedTheta.shifted_theta_bound (γ * t) θ₂ (mul_pos hγ ht))
  have e1 : (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) =
      fun v : ℤ × ℤ => Real.exp (-((α * t) * (v.1 + (θ₁ + l * v.2)) ^ 2)) *
        Real.exp (-((γ * t) * (v.2 + θ₂) ^ 2)) := by
    funext v
    rw [← Real.exp_add]
    congr 1
    unfold qForm
    ring
  have e2 : Real.pi / Real.sqrt (α * γ) / t =
      Real.sqrt (Real.pi / (α * t)) * Real.sqrt (Real.pi / (γ * t)) := by
    have hp := Real.pi_pos
    rw [← Real.sqrt_mul (by positivity)]
    symm
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have hs : Real.sqrt (α * γ) * Real.sqrt (α * γ) = α * γ := Real.mul_self_sqrt (by positivity)
    have hs0 : 0 < Real.sqrt (α * γ) := Real.sqrt_pos.mpr (by positivity)
    rw [div_div, div_mul_div_comm, div_mul_div_comm]
    congr 1
    linear_combination -t ^ 2 * hs
  rw [e1, e2]
  exact h

end GlobalTheory.Hk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaQFormStatement

section

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.summable_and_abs_tsum_exp_neg_qForm_sub_le : ∀ α γ l θ₁ θ₂ t : ℝ, 0 < α → 0 < γ → 0 < t → Summable (fun v : ℤ × ℤ => Real.exp (-(t * qForm α γ l θ₁ θ₂ v))) ∧ |∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) - Real.pi / Real.sqrt (α * γ) / t| ≤ Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2) := by
  first | exact @GlobalTheory.Hk.theta_qForm | exact GlobalTheory.Hk.theta_qForm | (intros; apply GlobalTheory.Hk.theta_qForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayCountThetaFibreCount

section

@[expose] public section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk

theorem rayCountTheta_fibre_count {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq1 : ∀ v, 1 ≤ q v) (hq : ∀ v, Q v = q v)
    (y : ℝ) (hy : 1 ≤ y) (hfin : {v | Q v ≤ y}.Finite) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) = (({v | Q v ≤ y}.ncard : ℕ) : ℝ) := by
  have hmaps : ∀ v ∈ hfin.toFinset, q v ∈ Finset.Icc 1 ⌊y⌋₊ := by
    intro v hv
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hq] at hv
    exact Finset.mem_Icc.mpr ⟨hq1 v, Nat.le_floor hv⟩
  have hfib : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊,
      {v | Q v = (n : ℕ)}.ncard = (hfin.toFinset.filter fun v => q v = n).card := by
    intro n hn
    rw [← Set.ncard_coe_finset]
    congr 1
    ext v
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset, hq, Nat.cast_inj]
    constructor
    · rintro rfl
      exact ⟨le_trans (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2) (Nat.floor_le (by linarith)), rfl⟩
    · exact fun h => h.2
  rw [show (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ)) =
      ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (((hfin.toFinset.filter fun v => q v = n).card : ℕ) : ℝ) from
    Finset.sum_congr rfl fun n hn => by rw [hfib n hn]]
  rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hmaps, ← Set.ncard_coe_finset,
    Set.Finite.coe_toFinset]

theorem rayCountTheta_fibre_tsum {ι : Type} (Q : ι → ℝ) (q : ι → ℕ) (hq : ∀ v, Q v = q v) (t : ℝ)
    (hs : Summable fun v => Real.exp (-(t * Q v))) :
    ∑' n : ℕ, (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n)) = ∑' v, Real.exp (-(t * Q v)) := by
  have hf := hs.hasSum.tsum_fiberwise q
  rw [← hf.tsum_eq]
  congr 1
  funext n
  have hset : {v | Q v = (n : ℕ)} = q ⁻¹' {n} := by
    ext v
    simp [hq]
  calc (({v | Q v = (n : ℕ)}.ncard : ℕ) : ℝ) * Real.exp (-(t * n))
      = ∑' _ : q ⁻¹' {n}, Real.exp (-(t * n)) := by
        rw [tsum_const, hset, Nat.card_coe_set_eq, nsmul_eq_mul]
    _ = ∑' b : q ⁻¹' {n}, Real.exp (-(t * Q b)) := by
        congr 1
        funext b
        rw [hq b, show q b = n from b.2]

theorem rayCountTheta : ∀ (K : Type) [Field K] [NumberField K] (d M : ℕ) (x : K), d.Prime → d % 4 = 3 → 100 ≤ d → x ^ 2 = -(d : K) → Module.finrank ℚ K = 2 → 3 ≤ M → ∀ D : RayData K M, ∀ g : D.G, (∀ y : ℝ, 1 ≤ y → |∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n - 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) * y| ≤ 10 * Real.sqrt y) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → |∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) - 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) / t| ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 * t := by
  intro K _ _ d M x hd hd4 hd100 hx hK hM D g
  obtain ⟨α, γ, l, θ₁, θ₂, hα, hγ, hαγ, hQ, ha⟩ := GlobalTheory.T.rayClassIdealCount_eq_ncard_shiftedBinaryForm K d M x hd hd4 hd100 hx hK hM D g
  choose q hq1 hq using hQ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hC : Real.pi / Real.sqrt (α * γ) = 2 * Real.pi / (Real.sqrt d * (M : ℝ) ^ 2) := by
    have hs : Real.sqrt (α * γ) = Real.sqrt d * (M : ℝ) ^ 2 / 2 := by
      rw [hαγ, show (d : ℝ) * (M : ℝ) ^ 4 / 4 = (Real.sqrt d * (M : ℝ) ^ 2 / 2) ^ 2 by
        rw [div_pow, mul_pow, Real.sq_sqrt hd0.le]; ring]
      exact Real.sqrt_sq (by positivity)
    have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
    rw [hs]
    field_simp
  refine ⟨fun y hy => ?_, fun t ht0 ht1 => ?_⟩
  · have h94 := GlobalTheory.T.abs_ncard_qForm_le_sub_pi_div_sqrt_mul_le_ten_sqrt α γ l θ₁ θ₂ y hα hγ hy
    have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, aRay D g n =
        (({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ y}.ncard : ℕ) : ℝ) := by
      simp only [ha]
      exact rayCountTheta_fibre_count (qForm α γ l θ₁ θ₂) q hq1 hq y hy h94.1
    rw [hsum, ← hC]
    exact h94.2
  · have h96 := GlobalTheory.T.summable_and_abs_tsum_exp_neg_qForm_sub_le α γ l θ₁ θ₂ t (by linarith) (by linarith) ht0
    have htsum : ∑' n : ℕ, aRay D g n * Real.exp (-(t * n)) =
        ∑' v : ℤ × ℤ, Real.exp (-(t * qForm α γ l θ₁ θ₂ v)) := by
      simp only [ha]
      exact rayCountTheta_fibre_tsum (qForm α γ l θ₁ θ₂) q hq t h96.1
    rw [htsum, ← hC]
    refine le_trans h96.2 ?_
    have hA : α ≤ α * γ := by nlinarith
    have hG : γ ≤ α * γ := by nlinarith
    have hP1 : 1 ≤ α * γ := by nlinarith
    have hsq : 1 ≤ Real.sqrt (α * γ) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hP1
    have hsq0 : 0 < Real.sqrt (α * γ) := by linarith
    have hCπ : Real.pi / Real.sqrt (α * γ) ≤ Real.pi := div_le_self Real.pi_pos.le hsq
    have hC0 : 0 ≤ Real.pi / Real.sqrt (α * γ) := by positivity
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have key : 3 * Real.pi * (α * γ) ^ 2 ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 := by
      rw [hαγ]
      have h1 : (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 10 := pow_le_pow_right₀ hd1 (by norm_num)
      have h2 : (M : ℝ) ^ 8 ≤ (M : ℝ) ^ 20 := pow_le_pow_right₀ hM1 (by norm_num)
      have hX : 0 ≤ (d : ℝ) ^ 10 * (M : ℝ) ^ 20 := by positivity
      calc 3 * Real.pi * ((d : ℝ) * (M : ℝ) ^ 4 / 4) ^ 2
          = (3 * Real.pi / 16) * ((d : ℝ) ^ 2 * (M : ℝ) ^ 8) := by ring
        _ ≤ 1 * ((d : ℝ) ^ 10 * (M : ℝ) ^ 20) :=
          mul_le_mul (by linarith [Real.pi_le_four]) (mul_le_mul h1 h2 (by positivity) (by positivity))
            (by positivity) (by norm_num)
        _ ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 := by
          rw [show (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 = 4 ^ 10 * ((d : ℝ) ^ 10 * (M : ℝ) ^ 20) by ring]
          linarith
    have hpoly : α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2 * t ^ 2 ≤ 3 * (α * γ) ^ 2 := by
      have e1 : α ^ 2 ≤ (α * γ) ^ 2 := pow_le_pow_left₀ (by linarith) hA 2
      have e2 : γ ^ 2 ≤ (α * γ) ^ 2 := pow_le_pow_left₀ (by linarith) hG 2
      have ht2 : t ^ 2 ≤ 1 := by nlinarith
      have e3 : α ^ 2 * γ ^ 2 * t ^ 2 ≤ (α * γ) ^ 2 := by
        calc α ^ 2 * γ ^ 2 * t ^ 2 = (α * γ) ^ 2 * t ^ 2 := by ring
          _ ≤ (α * γ) ^ 2 * 1 := mul_le_mul_of_nonneg_left ht2 (by positivity)
          _ = (α * γ) ^ 2 := by ring
      linarith
    calc Real.pi / Real.sqrt (α * γ) / t * ((α * t) ^ 2 + (γ * t) ^ 2 + (α * t) ^ 2 * (γ * t) ^ 2)
        = Real.pi / Real.sqrt (α * γ) * t * (α ^ 2 + γ ^ 2 + α ^ 2 * γ ^ 2 * t ^ 2) := by
          field_simp
      _ ≤ Real.pi * t * (3 * (α * γ) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hCπ ht0.le) hpoly (by positivity) (by positivity)
      _ = 3 * Real.pi * (α * γ) ^ 2 * t := by ring
      _ ≤ (4 * (d : ℝ) * (M : ℝ) ^ 2) ^ 10 * t := mul_le_mul_of_nonneg_right key ht0.le

end GlobalTheory.Hk
end
end
