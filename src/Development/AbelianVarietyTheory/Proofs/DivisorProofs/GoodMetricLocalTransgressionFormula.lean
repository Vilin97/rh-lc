module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundFamilyOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPolarisedTopFormDbarExactEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareCoordinateLengthMemIccAndPosStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedTopChernCoeffSlotLinearStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordHyp
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDerivCutoffConnectionDifferenceEq

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mdbar_neg_cut_conn_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    {G₀ G₁ : V n → Matrix r r ℂ} {v : V n} (hρ : DifferentiableAt ℝ ρ v) (h₀ : MContDiffAt 2 G₀ v)
    (u₀ : IsUnit (G₀ v).det) (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) :
    (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b))
      = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  funext a b
  have c₀ : MContDiffAt 1 (fun x => conn G₀ x (coordVec a)) v := h₀.conn u₀ (by norm_num) _
  have c₁ : MContDiffAt 1 (fun x => conn G₁ x (coordVec a)) v := h₁.conn u₁ (by norm_num) _
  have hρ' : DifferentiableAt ℝ (fun x => (ρ x : ℂ)) v := Complex.ofRealCLM.differentiableAt.comp v hρ
  have hs : mdbar (fun x => conn G₁ x (coordVec a) - conn G₀ x (coordVec a)) v (coordVec b) =
      mdbar (fun x => conn G₁ x (coordVec a)) v (coordVec b) -
        mdbar (fun x => conn G₀ x (coordVec a)) v (coordVec b) := by
    simp only [sub_eq_add_neg]
    rw [mdbar_add c₁ c₀.neg, mdbar_neg]
  rw [mdbar_neg (fun x => (ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a))),
    mdbar_smul hρ' (c₁.sub c₀), hs]
  simp only [Pi.sub_apply, Pi.smul_apply, curvAt, cutForm, curv, smul_sub, smul_neg]
  abel

end GlobalTheory.GoodTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDerivCutoffConnectionDifferenceEqStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, DifferentiableAt ℝ ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b)) = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | exact GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | (intros; apply GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMixTopSlotEqZero

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

set_option autoImplicit false

noncomputable def transConn {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    (G₀ G₁ : V n → Matrix r r ℂ) (j : Fin n) (i a : Fin n) : V n → Matrix r r ℂ :=
  if i < j then fun x => -conn G₁ x (coordVec a)
  else if i = j then fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))
  else fun x => -conn G₀ x (coordVec a)

theorem weighted_bound_cut_sum (x A B w C c : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ C) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hA : A * w ≤ c) (hB : B ≤ C) : x * (A + B) * w ≤ C * (|c| + C) := by
  have h1 : (A + B) * w ≤ |c| + C := by nlinarith [le_abs_self c]
  have hC : 0 ≤ C := hx0.trans hx
  rw [mul_assoc]
  exact mul_le_mul hx h1 (by positivity) hC

theorem weighted_bound_cut_entry (x X₁ X₀ d Y₁ Y₀ : ℂ) (wa wb C c : ℝ) (hx : ‖x‖ ≤ C) (hd : ‖d‖ ≤ C)
    (hX₁ : ‖X₁‖ * (wa * wb) ≤ c) (hX₀ : ‖X₀‖ ≤ C) (hY₁ : ‖Y₁‖ * wa ≤ c) (hY₀ : ‖Y₀‖ ≤ C)
    (hwa0 : 0 ≤ wa) (hwa1 : wa ≤ 1) (hwb0 : 0 ≤ wb) (hwb1 : wb ≤ 1) :
    ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb) ≤ 2 * C * (|c| + C) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hx
  have e1 := weighted_bound_cut_sum ‖x‖ ‖X₁‖ ‖X₀‖ (wa * wb) C c (norm_nonneg _) hx (norm_nonneg _) (norm_nonneg _)
    (by positivity) (by nlinarith) hX₁ hX₀
  have e2 := weighted_bound_cut_sum ‖d‖ ‖Y₁‖ ‖Y₀‖ wa C c (norm_nonneg _) hd (norm_nonneg _) (norm_nonneg _)
    hwa0 hwa1 hY₁ hY₀
  have n1 : ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ ≤ ‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  have hww : 0 ≤ wa * wb := by positivity
  have e2' : ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) ≤ C * (|c| + C) := by
    have h0 : 0 ≤ ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa := by positivity
    calc ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) = (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * wb := by ring
      _ ≤ (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * 1 := mul_le_mul_of_nonneg_left hwb1 h0
      _ ≤ C * (|c| + C) := by rw [mul_one]; exact e2
  calc ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb)
      ≤ (‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖)) * (wa * wb) := mul_le_mul_of_nonneg_right n1 hww
    _ = ‖x‖ * (‖X₁‖ + ‖X₀‖) * (wa * wb) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) := by ring
    _ ≤ C * (|c| + C) + C * (|c| + C) := add_le_add e1 e2'
    _ = 2 * C * (|c| + C) := by ring

theorem integral_mixTop_position_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → ∀ j : Fin n, IntegrableOn (fun v => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)) (offHyp S U) ∧ ∫ v in offHyp S U, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) = 0 := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK j
  obtain ⟨C, hC0, hC⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have h3 : (2 : WithTop ℕ∞) + 1 ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hw : ∀ v ∈ U, ∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1 :=
    fun v hv a => (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv)).1 a
  have hρd : ∀ v ∈ U, ContDiffAt ℝ ∞ ρ v := fun v hv => hρ.contDiffAt (hU.mem_nhds hv)
  have hρc : ∀ v ∈ U, ContDiffAt ℝ 2 (fun x => (ρ x : ℂ)) v := fun v hv =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hρd v hv).of_le h2)
  set θ := transConn ρ G₀ G₁ j with hθ
  have hsm : ∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v := by
    intro i a v hv
    have h1 := (hG₁ v hv).1.conn (j := 2) (hG₁ v hv).2 h3 (coordVec a)
    have h0 := (hG₀ v hv.1).1.conn (j := 2) (hG₀ v hv.1).2 h3 (coordVec a)
    simp only [hθ, transConn]
    split_ifs
    · exact h1.neg
    · exact (MContDiffAt.smul (hρc v hv.1) (h1.sub h0)).neg
    · exact h0.neg
  have heq : ∀ v ∈ offHyp S U, (fun i a b => mdbar (θ i a) v (coordVec b)) =
      intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j := by
    intro v hv
    funext i a b
    simp only [hθ, transConn, intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · rw [mdbar_neg]; rfl
    · exact congrFun (congrFun (GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq ((hρd v hv.1).differentiableAt (by simp))
        ((hG₀ v hv.1).1.of_le h2) (hG₀ v hv.1).2 ((hG₁ v hv).1.of_le h2) (hG₁ v hv).2) a) b
    · rw [mdbar_neg]; rfl
  have hzero : ∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0 := by
    intro a v hv hvK
    simp [hθ, transConn, hρK v hv.1 hvK]
  have hcC : 0 ≤ C * (|c| + C) := by positivity
  have hbd1 : ∀ v ∈ offHyp S U, v ∈ K → ∀ a p q,
      ‖θ j a v p q‖ * poinWt S v a ≤ |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK a p q
    obtain ⟨hρv, -, hc0, -⟩ := hC v hvK
    simp only [hθ, transConn, lt_irrefl, if_false, if_true, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e := weighted_bound_cut_sum |ρ v| ‖conn G₁ v (coordVec a) p q‖ ‖conn G₀ v (coordVec a) p q‖ (poinWt S v a) C c
      (abs_nonneg _) hρv (norm_nonneg _) (norm_nonneg _) (hw v hv.1 a).1 (hw v hv.1 a).2
      (hconn v hv a p q) (hc0 a p q)
    have n1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)) (abs_nonneg (ρ v)))
      (hw v hv.1 a).1
    have : 0 ≤ |c| := abs_nonneg c
    nlinarith
  have hbd2 : ∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q,
      ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤
        |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK i a b p q
    obtain ⟨hρv, hdv, hc0, hk0⟩ := hC v hvK
    obtain ⟨hwa0, hwa1⟩ := hw v hv.1 a
    obtain ⟨hwb0, hwb1⟩ := hw v hv.1 b
    have hww : 0 ≤ poinWt S v a * poinWt S v b := by positivity
    have hww1 : poinWt S v a * poinWt S v b ≤ 1 := by nlinarith
    have hca : 0 ≤ |c| := abs_nonneg c
    rw [show mdbar (θ i a) v (coordVec b) = _ from congrFun (congrFun (congrFun (heq v hv) i) a) b]
    simp only [intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · have := hcurv v hv a b p q
      simp only [curvAt]
      nlinarith [le_abs_self c]
    · simp only [curvAt, cutForm, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul]
      have e := weighted_bound_cut_entry (ρ v : ℂ) (curv G₁ v (coordVec a) (coordVec b) p q) (curv G₀ v (coordVec a) (coordVec b) p q)
        (dbar (fun x => (ρ x : ℂ)) v (coordVec b)) (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
        (poinWt S v a) (poinWt S v b) C c (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hρv) (hdv b)
        (hcurv v hv a b p q) (hk0 a b p q) (hconn v hv a p q) (hc0 a p q) hwa0 hwa1 hwb0 hwb1
      nlinarith
    · simp only [curvAt]
      have := hk0 a b p q
      have := mul_le_mul_of_nonneg_left hww1 (norm_nonneg (curv G₀ v (coordVec a) (coordVec b) p q))
      nlinarith
  obtain ⟨hi, hint⟩ := GlobalTheory.T.integral_polarisedTopForm_dbarExact_eq_zero S U K θ j (|c| + C + 2 * C * (|c| + C)) hU hK hKU hsmall hsm hzero
    hbd1 hbd2
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  refine ⟨hi.congr_fun (fun v hv => congrArg mixTop (heq v hv)) hO, ?_⟩
  rw [← hint]
  exact setIntegral_congr_fun hO fun v hv => congrArg mixTop (heq v hv).symm

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPolarisedTopChernCoeffTransgressionTelescope

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_mixTop_position_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) :
    ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = mixTop (fun _ => K₁) - mixTop fun _ => K₀ := by
  classical
  set T : ℕ → ℂ := fun k => mixTop (fun i : Fin n => if (i : ℕ) < k then K₁ else K₀) with hT
  have hterm : ∀ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = T ((j : ℕ) + 1) - T j := by
    intro j
    have hK : K₁ - K₀ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₀ := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [hK, GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ K₁ K₀ 1 (-1) j, one_mul, neg_one_mul, ← sub_eq_add_neg]
    congr 1
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j + 1 := by have := Fin.lt_def.mp h1; omega
        simp [h1, this]
      · by_cases h2 : i = j
        · subst h2; simp
        · have h3 : ¬ ((i : ℕ) < j + 1) := by
            have : j < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
            have := Fin.lt_def.mp this; omega
          simp [h1, h2, h3]
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j := Fin.lt_def.mp h1
        simp [h1, this]
      · have : ¬ ((i : ℕ) < j) := fun h => h1 (Fin.lt_def.mpr h)
        by_cases h2 : i = j
        · simp [h1, h2, this]
        · simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun k => T (k + 1) - T k) n, Finset.sum_range_sub]
  have e1 : (fun i : Fin n => if (i : ℕ) < n then K₁ else K₀) = fun _ => K₁ := by
    funext i; simp [i.isLt]
  have e0 : (fun i : Fin n => if (i : ℕ) < 0 then K₁ else K₀) = fun _ => K₀ := by
    funext i; simp
  show mixTop _ - mixTop _ = _
  rw [e1, e0]

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormula

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mixTop_slot_smul_sub_sub {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (A B D : _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r) (s : ℂ) (j : Fin n) :
    _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (s • (A - B) - D) B j) =
      s * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (A - B) B j) +
        (-1) * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A D B j) := by
  rw [← _root_.GlobalTheory.GoodTop.mixTop_position_linear, neg_one_smul, ← sub_eq_add_neg]


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodTop.integral_cutTop_sub : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ * _root_.GlobalTheory.GoodMetric.poinWt S v a ≤ c) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ * (_root_.GlobalTheory.GoodMetric.poinWt S v a * _root_.GlobalTheory.GoodMetric.poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) = ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hS hG₀ hG₁ hconn hcurv hρ hρK
  have hstokes := _root_.GlobalTheory.GoodTop.integral_mixTop_position_eq_zero S U K G₀ G₁ ρ c hU hK hKU
    hS hG₀ hG₁ hconn hcurv hρ hρK
  have hF₁ := _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hF₀ := (_root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth U K G₀ ρ hU hK hKU hG₀ hρ
    hρK).mono_set (fun v hv => ((mem_offHyp_iff (S := S)).1 hv).1)
  have hT := _root_.GlobalTheory.GoodTop.integrableOn_corrC S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hpt : ∀ v, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v =
      ∑ j, _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ v)
        ((ρ v : ℂ) • (_root_.GlobalTheory.GoodTop.curvAt G₁ v - _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
          _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ v) (_root_.GlobalTheory.GoodTop.curvAt G₀ v) j) := by
    intro v
    simp_rw [mixTop_slot_smul_sub_sub]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      _root_.GlobalTheory.GoodTop.sum_mixTop_position_sub]
    unfold _root_.GlobalTheory.GoodTop.corrC
    ring
  have hzero : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun j _ => (hstokes j).1]
    exact Finset.sum_eq_zero fun j _ => (hstokes j).2
  have hsplit : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) =
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
    have hsub : IntegrableOn (fun v =>
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v))
        (_root_.GlobalTheory.GoodTop.offHyp S U) := hF₁.sub hF₀
    exact (integral_sub hsub hT).trans (congrArg (· - _) (integral_sub hF₁ hF₀))
  rw [← setIntegral_congr_set (_root_.GlobalTheory.GoodTop.offHyp_ae_eq S U)]
  linear_combination hzero - hsplit

end GlobalTheory.GoodTop
end
end
