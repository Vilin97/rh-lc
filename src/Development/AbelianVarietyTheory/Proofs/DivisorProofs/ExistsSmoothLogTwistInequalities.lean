module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalities

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.ConcaveTwist

noncomputable def twShift (T : ℝ) : ℝ := Real.log (1 + Real.exp (-T))

noncomputable def twV (T y : ℝ) : ℝ := y + twShift T - Real.log (1 + Real.exp (y - T))

noncomputable def twP (T y : ℝ) : ℝ := (1 + Real.exp (y - T))⁻¹

noncomputable def twEta (T y : ℝ) : ℝ := 2 + twV T y + Real.log (1 + twV T y)

noncomputable def twEta1 (T y : ℝ) : ℝ := twP T y * (1 + (1 + twV T y)⁻¹)

noncomputable def twEta2 (T y : ℝ) : ℝ :=
  -(twP T y * (1 - twP T y)) * (1 + (1 + twV T y)⁻¹) - twP T y * (twP T y * ((1 + twV T y) ^ 2)⁻¹)

lemma logistic_pos (T y : ℝ) : 0 < twP T y := inv_pos.mpr (by positivity)

lemma twistMap_add_mul (T y : ℝ) : (1 + Real.exp (y - T)) * twP T y = 1 := by
  unfold twP; exact mul_inv_cancel₀ (by positivity)

lemma logistic_lt_one (T y : ℝ) : twP T y < 1 := by
  have h := twistMap_add_mul T y
  have := logistic_pos T y
  nlinarith [Real.exp_pos (y - T)]

lemma twShift_nonneg (T : ℝ) : 0 ≤ twShift T :=
  Real.log_nonneg (by linarith [Real.exp_pos (-T)])

lemma twShift_le_one (T : ℝ) (hT : 0 ≤ T) : twShift T ≤ 1 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-T) by positivity)
  have h2 : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold twShift; linarith

lemma twV_ge_self (T y : ℝ) (hy : y ≤ 0) : y ≤ twV T y := by
  have : Real.log (1 + Real.exp (y - T)) ≤ twShift T := by
    unfold twShift
    apply Real.log_le_log (by positivity)
    have := Real.exp_le_exp.mpr (show y - T ≤ -T by linarith)
    linarith
  unfold twV; linarith

lemma twV_nonneg (T y : ℝ) (hy : 0 ≤ y) : 0 ≤ twV T y := by
  have he : Real.exp (y - T) = Real.exp y * Real.exp (-T) := by
    rw [← Real.exp_add]; ring_nf
  have h1 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have : Real.log (1 + Real.exp (y - T)) ≤ y + twShift T := by
    have hr : y + twShift T = Real.log (Real.exp y * (1 + Real.exp (-T))) := by
      rw [Real.log_mul (Real.exp_pos y).ne' (by positivity), Real.log_exp]; rfl
    rw [hr]
    apply Real.log_le_log (by positivity)
    rw [he]; nlinarith [Real.exp_pos (-T)]
  unfold twV; linarith

lemma twV_le (T y : ℝ) (hT : 0 ≤ T) : twV T y ≤ T + 1 := by
  have : y - T ≤ Real.log (1 + Real.exp (y - T)) := by
    calc y - T = Real.log (Real.exp (y - T)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  have := twShift_le_one T hT
  unfold twV; linarith

lemma twV_le_self (T y : ℝ) (hy : 0 ≤ y) : twV T y ≤ y := by
  have : twShift T ≤ Real.log (1 + Real.exp (y - T)) := by
    unfold twShift
    apply Real.log_le_log (by positivity)
    have := Real.exp_le_exp.mpr (show -T ≤ y - T by linarith)
    linarith
  unfold twV; linarith

lemma twV_gt (T y : ℝ) (hy : -1/4 < y) : -1/4 < twV T y := by
  rcases le_total y 0 with h | h
  · linarith [twV_ge_self T y h]
  · linarith [twV_nonneg T y h]

lemma twV_ge_T_sub_two (T y : ℝ) (h1 : T - 1 ≤ y) (h2 : y ≤ T + 1) : T - 2 ≤ twV T y := by
  set q := Real.exp (y - T) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hqe : 1 ≤ q * Real.exp 1 := by
    rw [hq, ← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hE : Real.exp (y - T + 2) = q * Real.exp 1 * Real.exp 1 := by
    rw [show y - T + 2 = (y - T) + 1 + 1 by ring, Real.exp_add, Real.exp_add]
  have : Real.log (1 + q) ≤ y - T + 2 := by
    calc Real.log (1 + q) ≤ Real.log (Real.exp (y - T + 2)) := by
          apply Real.log_le_log (by positivity)
          rw [hE]
          nlinarith [mul_nonneg hq0.le (show 0 ≤ Real.exp 1 * Real.exp 1 - Real.exp 1 - 1 by nlinarith)]
      _ = y - T + 2 := Real.log_exp _
  have := twShift_nonneg T
  unfold twV; rw [← hq]; linarith

lemma hasDerivAt_twV (T y : ℝ) : HasDerivAt (twV T) (twP T y) y := by
  have h1 : HasDerivAt (fun y => Real.exp (y - T)) (Real.exp (y - T)) y := by
    simpa using ((hasDerivAt_id y).sub_const T).exp
  have h2 : HasDerivAt (fun y => Real.log (1 + Real.exp (y - T)))
      (Real.exp (y - T) / (1 + Real.exp (y - T))) y := by
    simpa using (h1.const_add 1).log (by positivity)
  have h3 := ((hasDerivAt_id y).add_const (twShift T)).sub h2
  refine h3.congr_deriv ?_
  have : (1 + Real.exp (y - T)) ≠ 0 := by positivity
  unfold twP; field_simp; ring

lemma hasDerivAt_twP (T y : ℝ) : HasDerivAt (twP T) (-(twP T y * (1 - twP T y))) y := by
  have h1 : HasDerivAt (fun y => Real.exp (y - T)) (Real.exp (y - T)) y := by
    simpa using ((hasDerivAt_id y).sub_const T).exp
  have h2 := (h1.const_add 1).inv (show (1 + Real.exp (y - T)) ≠ 0 by positivity)
  refine h2.congr_deriv ?_
  have : (1 + Real.exp (y - T)) ≠ 0 := by positivity
  unfold twP; field_simp; ring

lemma hasDerivAt_twEta (T y : ℝ) (h : 0 < 1 + twV T y) :
    HasDerivAt (twEta T) (twEta1 T y) y := by
  have hv := hasDerivAt_twV T y
  have h2 := (hv.const_add 2).add ((hv.const_add 1).log h.ne')
  refine h2.congr_deriv ?_
  unfold twEta1; ring

lemma hasDerivAt_twEta1 (T y : ℝ) (h : 0 < 1 + twV T y) :
    HasDerivAt (twEta1 T) (twEta2 T y) y := by
  have hv := hasDerivAt_twV T y
  have hp := hasDerivAt_twP T y
  have h2 := hp.mul (((hv.const_add 1).inv h.ne').const_add 1)
  refine h2.congr_deriv ?_
  unfold twEta2; simp only [Pi.inv_apply]; ring

lemma contDiff_twV (T : ℝ) : ContDiff ℝ ∞ (twV T) := by
  have h : ContDiff ℝ ∞ (fun y : ℝ => 1 + Real.exp (y - T)) :=
    contDiff_const.add ((contDiff_id.sub contDiff_const).exp)
  exact (contDiff_id.add contDiff_const).sub (h.log fun y => by positivity)

end GlobalTheory.ConcaveTwist

namespace GlobalTheory.ConcaveTwist

lemma contDiffOn_twEta (T : ℝ) : ContDiffOn ℝ ∞ (twEta T) (Set.Ioi (-1/4)) := by
  have hv := contDiff_twV T
  have h1 : ContDiff ℝ ∞ (fun y => 1 + twV T y) := contDiff_const.add hv
  exact ((contDiff_const.add hv).contDiffOn).add
    (h1.contDiffOn.log fun y hy => by have := twV_gt T y hy; linarith)

lemma twEta_pos (T y : ℝ) (hy : -1/4 < y) : 0 < twEta T y := by
  have hv := twV_gt T y hy
  have hw : 0 < 1 + twV T y := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hw
  have hi : (1 + twV T y)⁻¹ < 4/3 := by
    rw [inv_lt_comm₀ hw (by norm_num)]; linarith
  unfold twEta; linarith

lemma twEta_bounds (T y : ℝ) (hT : 0 ≤ T) (hy : 0 ≤ y) :
    0 ≤ twEta1 T y ∧ twEta1 T y ≤ 2 ∧ 2 ≤ twEta T y ∧ twEta2 T y < 0 ∧
      twEta T y ≤ 2 + 2 * min y (T + 1) ∧
      twEta T y + twEta1 T y ^ 2 / (-twEta2 T y) ≤ 8 * (1 + (min y (T + 1)) ^ 2) := by
  have hv0 := twV_nonneg T y hy
  have hvm : twV T y ≤ min y (T + 1) := le_min (twV_le_self T y hy) (twV_le T y hT)
  have hp0 := logistic_pos T y
  have hp1 := logistic_lt_one T y
  set v := twV T y with hvdef
  set p := twP T y with hpdef
  set m := min y (T + 1) with hmdef
  have hw : 0 < 1 + v := by linarith
  set r := (1 + v)⁻¹ with hrdef
  have hr0 : 0 < r := inv_pos.mpr hw
  have hwr : (1 + v) * r = 1 := mul_inv_cancel₀ hw.ne'
  have hr1 : r ≤ 1 := by nlinarith
  have hr2 : ((1 + v) ^ 2)⁻¹ = r ^ 2 := by rw [inv_pow]
  have hη1 : twEta1 T y = p * (1 + r) := rfl
  have hη2 : -twEta2 T y = p * (1 - p) * (1 + r) + p ^ 2 * r ^ 2 := by
    unfold twEta2; rw [← hvdef, ← hpdef, hr2]; ring
  have hη : twEta T y = 2 + v + Real.log (1 + v) := rfl
  have hlog0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
  have hlogv : Real.log (1 + v) ≤ v := by
    have := Real.log_le_sub_one_of_pos hw; linarith
  have hneg : 0 < -twEta2 T y := by
    rw [hη2]; have := mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) (by linarith : (0:ℝ) < 1 + r)
    positivity
  have key : (2 + v) * r = 1 + r := by linear_combination hwr
  have key2 : ((2 + v) * r) ^ 2 = (1 + r) ^ 2 := by rw [key]
  have hratio : twEta1 T y ^ 2 / (-twEta2 T y) ≤ (2 + v) ^ 2 := by
    rw [div_le_iff₀ hneg]
    have e : (2 + v) ^ 2 * (-twEta2 T y) - twEta1 T y ^ 2 = (2 + v) ^ 2 * (p * (1 - p) * (1 + r)) := by
      rw [hη2, hη1]; linear_combination p ^ 2 * key2
    have : 0 ≤ (2 + v) ^ 2 * (p * (1 - p) * (1 + r)) := by
      have := sub_pos.mpr hp1; positivity
    linarith
  have hvm2 : v ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hv0 hvm 2
  refine ⟨by rw [hη1]; positivity, by rw [hη1]; nlinarith, by rw [hη]; linarith, by linarith,
    by rw [hη]; linarith, ?_⟩
  rw [hη]
  nlinarith [sq_nonneg (v - 3/7)]

lemma twEta_mid (T y : ℝ) (hT : 2 ≤ T) (h1 : T - 1 ≤ y) (h2 : y ≤ T + 1) :
    3 / 16 ≤ -twEta2 T y ∧ T ≤ twEta T y := by
  have hv := twV_ge_T_sub_two T y h1 h2
  have hv0 : 0 ≤ twV T y := by linarith
  have hp0 := logistic_pos T y
  have hp1 := logistic_lt_one T y
  have hpw := twistMap_add_mul T y
  set v := twV T y with hvdef
  set p := twP T y with hpdef
  set q := Real.exp (y - T) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hq3 : q ≤ 3 := by
    have : q ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hqe : 1 ≤ q * Real.exp 1 := by
    rw [hq, ← Real.exp_add]; exact Real.one_le_exp (by linarith)
  have hq13 : 1 / 3 ≤ q := by nlinarith
  have hw : 0 < 1 + v := by linarith
  set r := (1 + v)⁻¹ with hrdef
  have hr0 : 0 < r := inv_pos.mpr hw
  have hr2 : ((1 + v) ^ 2)⁻¹ = r ^ 2 := by rw [inv_pow]
  have hη2 : -twEta2 T y = p * (1 - p) * (1 + r) + p ^ 2 * r ^ 2 := by
    unfold twEta2; rw [← hvdef, ← hpdef, hr2]; ring
  have h1p : 1 - p = q * p := by linear_combination (-1 : ℝ) * hpw
  have hpw2 : ((1 + q) * p) ^ 2 = 1 := by rw [hpw]; norm_num
  have e : q * p ^ 2 * 16 - 3 = p ^ 2 * (3 * q - 1) * (3 - q) := by
    linear_combination 3 * hpw2
  have hmain : 3 / 16 ≤ p * (1 - p) := by
    rw [h1p]
    have : 0 ≤ p ^ 2 * (3 * q - 1) * (3 - q) := by
      have a : 0 ≤ 3 * q - 1 := by linarith
      have b : 0 ≤ 3 - q := by linarith
      positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [hη2]
    have : 0 ≤ p * (1 - p) * r := by have := sub_pos.mpr hp1; positivity
    nlinarith [sq_nonneg (p * r)]
  · have hlog0 : 0 ≤ Real.log (1 + v) := Real.log_nonneg (by linarith)
    show T ≤ 2 + v + Real.log (1 + v)
    linarith

end GlobalTheory.ConcaveTwist


open GlobalTheory.ConcaveTwist in
theorem GlobalTheory.concave_twist_exists : ∀ T : ℝ, 300 ≤ T → ∃ η η1 η2 : ℝ → ℝ, ContDiffOn ℝ ∞ η (Set.Ioi (-1/4)) ∧ (∀ y, -1/4 < y → 0 < η y ∧ HasDerivAt η (η1 y) y ∧ HasDerivAt η1 (η2 y) y) ∧ (∀ y, 0 ≤ y → 0 ≤ η1 y ∧ η1 y ≤ 2 ∧ 2 ≤ η y ∧ η2 y < 0 ∧ η y ≤ 2 + 2 * min y (T + 1) ∧ η y + η1 y ^ 2 / (-η2 y) ≤ 8 * (1 + (min y (T + 1)) ^ 2)) ∧ (∀ y, T - 1 ≤ y → y ≤ T + 1 → 3 / 16 ≤ -η2 y ∧ T ≤ η y) := by
  intro T hT
  refine ⟨twEta T, twEta1 T, twEta2 T, contDiffOn_twEta T, ?_, ?_, ?_⟩
  · intro y hy
    have hw : 0 < 1 + twV T y := by linarith [twV_gt T y hy]
    exact ⟨twEta_pos T y hy, hasDerivAt_twEta T y hw, hasDerivAt_twEta1 T y hw⟩
  · intro y hy
    exact twEta_bounds T y (by linarith) hy
  · intro y h1 h2
    exact twEta_mid T y (by linarith) h1 h2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalitiesStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_concaveTwist_eta_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ η η1 η2 : ℝ → ℝ, ContDiffOn ℝ ∞ η (Set.Ioi (-1/4)) ∧ (∀ y, -1/4 < y → 0 < η y ∧ HasDerivAt η (η1 y) y ∧ HasDerivAt η1 (η2 y) y) ∧ (∀ y, 0 ≤ y → 0 ≤ η1 y ∧ η1 y ≤ 2 ∧ 2 ≤ η y ∧ η2 y < 0 ∧ η y ≤ 2 + 2 * min y (T + 1) ∧ η y + η1 y ^ 2 / (-η2 y) ≤ 8 * (1 + (min y (T + 1)) ^ 2)) ∧ (∀ y, T - 1 ≤ y → y ≤ T + 1 → 3 / 16 ≤ -η2 y ∧ T ≤ η y) := by
  first | exact @GlobalTheory.concave_twist_exists | exact GlobalTheory.concave_twist_exists | (intros; apply GlobalTheory.concave_twist_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalities

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

private lemma twist_estimate_first (a b e M : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 2 ≤ e) (hb : 0 < b)
    (hM : 0 ≤ M) (h : e + a ^ 2 / b ≤ 8 * (1 + M)) :
    0 ≤ a / e ∧ a / e ≤ 1 ∧ 0 < (b * e + a ^ 2) / e ^ 2 ∧ (a / e) ^ 2 ≤ (b * e + a ^ 2) / e ^ 2 ∧
      1 / (1 + M) / 8 ≤ (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  refine ⟨by positivity, ?_, by positivity, ?_, ?_⟩
  · rw [div_le_one he0]; linarith
  · rw [div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 < b * e := by positivity
    linarith
  · have e1 : (1 - (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2)) * e⁻¹ = 1 / (e + a ^ 2 / b) := by
      field_simp
      ring
    have e2 : 1 / (1 + M) / 8 = 1 / (8 * (1 + M)) := by
      field_simp
    rw [e1, e2]
    exact one_div_le_one_div_of_le (by positivity) h

private lemma twist_estimate_second (a b e m : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (he : 300 ≤ e) (hb : 3 / 16 ≤ b)
    (h : e ≤ 2 + 2 * m) :
    e⁻¹ / ((b * e + a ^ 2) / e ^ 2) ≤ 16 / 3 ∧
      1 / (1 + m ^ 2) / 8 ≤ (1 - 5 * ((a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2))) * e⁻¹ := by
  have he0 : 0 < e := by linarith
  have hb0 : 0 < b := by linarith
  have hD : 0 < b * e + a ^ 2 := by positivity
  have hbe : 3 / 16 * e ≤ b * e := mul_le_mul_of_nonneg_right hb he0.le
  have ha4 : a ^ 2 ≤ 4 := by nlinarith
  have ha0 : 0 ≤ a ^ 2 := by positivity
  constructor
  · have e1 : e⁻¹ / ((b * e + a ^ 2) / e ^ 2) = e / (b * e + a ^ 2) := by
      field_simp
    rw [e1, div_le_iff₀ hD]
    linarith
  · have e1 : (a / e) ^ 2 / ((b * e + a ^ 2) / e ^ 2) = a ^ 2 / (b * e + a ^ 2) := by
      field_simp
    have h1 : a ^ 2 / (b * e + a ^ 2) ≤ 1 / 10 := by
      rw [div_le_iff₀ hD]; linarith
    have e2 : 1 / (1 + m ^ 2) / 8 = 1 / 2 * (4 * (1 + m ^ 2))⁻¹ := by
      field_simp
      norm_num
    have h2 : (4 * (1 + m ^ 2))⁻¹ ≤ e⁻¹ := by
      apply inv_anti₀ he0
      nlinarith [sq_nonneg (m - 1 / 4)]
    rw [e1, e2]
    apply mul_le_mul (by linarith) h2 (by positivity) (by linarith)

theorem exists_log_twist : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  intro T hT
  obtain ⟨η, η1, η2, hs, hd, hp, hw⟩ := GlobalTheory.T.exists_concaveTwist_eta_inequalities T hT
  set κ : ℝ → ℝ := fun x => Real.smoothTransition (2 - 16 * x) * (-Real.log (η (-x))) with hκ
  have hloc : ∀ x : ℝ, x < 1 / 16 → κ x = -Real.log (η (-x)) := by
    intro x hx
    simp only [hκ]
    rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  have hη : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η (-x)) (-η1 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.1
    have h' := HasDerivAt.comp x (h₂ := η) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hη1 : ∀ x : ℝ, x < 1 / 16 → HasDerivAt (fun x => η1 (-x)) (-η2 (-x)) x := by
    intro x hx
    have h := (hd (-x) (by linarith)).2.2
    have h' := HasDerivAt.comp x (h₂ := η1) (h := fun x : ℝ => -x) h (hasDerivAt_neg x)
    simpa [Function.comp_def] using h'
  have hd1 : ∀ x : ℝ, x < 1 / 16 → deriv κ x = η1 (-x) / η (-x) := by
    intro x hx
    have hev : κ =ᶠ[𝓝 x] fun x => -Real.log (η (-x)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hloc y hy
    rw [hev.deriv_eq]
    have h := ((hη x hx).log (hd (-x) (by linarith)).1.ne').neg
    have h2 : HasDerivAt (fun x => -Real.log (η (-x))) (-(-η1 (-x) / η (-x))) x := h
    rw [h2.deriv]; ring
  have hd2 : ∀ x : ℝ, x < 1 / 16 →
      deriv (deriv κ) x = ((-η2 (-x)) * η (-x) + η1 (-x) ^ 2) / η (-x) ^ 2 := by
    intro x hx
    have hev : deriv κ =ᶠ[𝓝 x] fun x => η1 (-x) / η (-x) := by
      filter_upwards [Iio_mem_nhds hx] with y hy using hd1 y hy
    rw [hev.deriv_eq]
    have h2 : HasDerivAt (fun x => η1 (-x) / η (-x)) _ x :=
      (hη1 x hx).div (hη x hx) (hd (-x) (by linarith)).1.ne'
    rw [h2.deriv]; ring
  have hexp : ∀ x : ℝ, x < 1 / 16 → Real.exp (κ x) = (η (-x))⁻¹ := by
    intro x hx
    rw [hloc x hx, Real.exp_neg, Real.exp_log (hd (-x) (by linarith)).1]
  have hwT : ∀ x : ℝ, x ≤ 0 → wT T x = 1 / (1 + (min (-x) (T + 1)) ^ 2) := by
    intro x hx
    unfold wT
    congr 2
    rcases le_total (-x) (T + 1) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith)]; ring
    · rw [min_eq_right h, min_eq_right (by nlinarith)]
  refine ⟨κ, ?_, ⟨Real.log (2 * T + 4), ?_⟩, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < 1 / 4
    · have h1 : ContDiffAt ℝ ∞ η (-x) :=
        hs.contDiffAt (Ioi_mem_nhds (by linarith))
      have h2 : ContDiffAt ℝ ∞ (fun x : ℝ => η (-x)) x :=
        ContDiffAt.comp x (g := η) (f := fun x : ℝ => -x) h1 contDiff_neg.contDiffAt
      have h3 := (h2.log (hd (-x) (by linarith)).1.ne').neg
      have h4 : ContDiff ℝ ∞ (fun x : ℝ => Real.smoothTransition (2 - 16 * x)) :=
        Real.smoothTransition.contDiff.comp (by fun_prop)
      exact h4.contDiffAt.mul h3
    · have hev : κ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds (show (1 / 8 : ℝ) < x by linarith)] with y hy
        have hy' : (1 / 8 : ℝ) < y := hy
        simp only [hκ]
        rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro x hx
    obtain ⟨-, -, h2, -, h3, -⟩ := hp (-x) (by linarith)
    rw [hloc x (by linarith), abs_neg, abs_of_nonneg (Real.log_nonneg (by linarith))]
    apply Real.log_le_log (by linarith)
    have := min_le_right (-x) (T + 1)
    linarith
  · intro x hx
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, h2, h3, -, h5⟩ := hp (-x) (by linarith)
    rw [hd1 x hx', hd2 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_first _ _ _ _ h0 h1 h2 (by linarith) (sq_nonneg _) h5
  · intro x hx1 hx2
    have hx : x ≤ 0 := by linarith
    have hx' : x < 1 / 16 := by linarith
    obtain ⟨h0, h1, -, -, h4, -⟩ := hp (-x) (by linarith)
    obtain ⟨h6, h7⟩ := hw (-x) (by linarith) (by linarith)
    rw [hd2 x hx', hd1 x hx', hexp x hx', hwT x hx]
    exact twist_estimate_second _ _ _ _ h0 h1 (by linarith) h6 h4

end GlobalTheory.OTY
end
end
