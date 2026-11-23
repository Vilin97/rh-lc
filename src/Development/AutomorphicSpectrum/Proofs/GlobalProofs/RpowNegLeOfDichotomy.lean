module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.RealPlaceAnalysis.FinalF
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

-- Source module: Development.AutomorphicSpectrum.Proofs.HermitianForms.OneAddHsInvPowLintegralLtTop

section

@[expose] public section

open MeasureTheory Matrix Finset PI.UpqRep
open scoped InnerProductSpace ENNReal ComplexOrder

namespace GlobalTheory.CompanionTheory.HolPQ

theorem muG_hs_ball_le (n : ℕ) (ε : Fin n → Bool) :
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      muG ε {g | hs (umat g) ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2)) :=
  Formalism.REAL.volume_growth n ε

theorem continuous_hs_umat {n : ℕ} (ε : Fin n → Bool) :
    Continuous fun g : UJ ε => hs (umat g) := by
  have hc : Continuous (coeMatrixAlt ε) := continuous_coeMatrix ε
  unfold hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (Continuous.matrix_elem hc i j).norm.pow 2

theorem lintegral_one_add_inv_pow_lt_top {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (h : X → ℝ) (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x) (d : ℕ) (C : ℝ)
    (hC : ∀ k : ℕ, μ {x | h x ≤ (4 : ℝ) ^ k} ≤ ENNReal.ofReal (C * ((4 : ℝ) ^ k) ^ d))
    (s : ℕ) (hs' : d + 1 ≤ s) :
    ∫⁻ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ∂μ < ⊤ := by
  set c : ℕ → ℝ := fun k => (4 : ℝ) ^ s * (((4 : ℝ) ^ k)⁻¹) ^ s with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by simp only [hc]; positivity
  set A : ℕ → Set X := fun k => {x | h x ≤ (4 : ℝ) ^ k} with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k => measurableSet_le hm measurable_const
  have point : ∀ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ≤
      ∑' k, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x := by
    intro x
    have hex : ∃ k : ℕ, h x ≤ (4 : ℝ) ^ k := by
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (h x) (by norm_num : (1 : ℝ) < 4)
      exact ⟨k, hk.le⟩
    classical
    set k := Nat.find hex with hk
    have hxk : x ∈ A k := Nat.find_spec hex
    refine le_trans ?_ (ENNReal.le_tsum k)
    rw [Set.indicator_of_mem hxk]
    apply ENNReal.ofReal_le_ofReal
    have h4 : (4 : ℝ) ^ k ≤ 4 * (1 + h x) := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0]; have := h0 x; norm_num; linarith
      · have hmin : ¬ h x ≤ (4 : ℝ) ^ (k - 1) := Nat.find_min hex (by omega)
        have e : (4 : ℝ) ^ k = 4 * 4 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [e]; push Not at hmin; linarith
    have hpos : 0 < 1 + h x := by have := h0 x; linarith
    have h5 : (1 + h x)⁻¹ ≤ 4 * ((4 : ℝ) ^ k)⁻¹ := by
      rw [inv_le_comm₀ hpos (by positivity), mul_inv, inv_inv]
      have : (0 : ℝ) < 4 ^ k := by positivity
      nlinarith
    calc ((1 + h x)⁻¹) ^ s ≤ (4 * ((4 : ℝ) ^ k)⁻¹) ^ s :=
          pow_le_pow_left₀ (by positivity) h5 s
      _ = c k := by simp only [hc]; rw [mul_pow]
  set C' : ℝ := max C 0 with hC'
  have hterm : ∀ k, ENNReal.ofReal (c k) * μ (A k) ≤
      ENNReal.ofReal ((4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k) := by
    intro k
    have h1 : μ (A k) ≤ ENNReal.ofReal (C' * ((4 : ℝ) ^ k) ^ d) :=
      (hC k).trans (ENNReal.ofReal_le_ofReal (by
        gcongr; exact le_max_left _ _))
    calc ENNReal.ofReal (c k) * μ (A k)
        ≤ ENNReal.ofReal (c k) * ENNReal.ofReal (C' * ((4 : ℝ) ^ k) ^ d) := by gcongr
      _ = ENNReal.ofReal (c k * (C' * ((4 : ℝ) ^ k) ^ d)) :=
          (ENNReal.ofReal_mul (hc0 k)).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hC0 : 0 ≤ C' := le_max_right _ _
          have hq : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
          have key : (((4 : ℝ) ^ k)⁻¹) ^ s * ((4 : ℝ) ^ k) ^ d ≤ ((4 : ℝ)⁻¹) ^ k := by
            obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs'
            have e : (((4 : ℝ) ^ k)⁻¹) ^ (d + 1 + t) * ((4 : ℝ) ^ k) ^ d =
                ((4 : ℝ) ^ k)⁻¹ * (((4 : ℝ) ^ k)⁻¹) ^ t := by
              have : ((4 : ℝ) ^ k) ≠ 0 := by positivity
              rw [pow_add, pow_succ, inv_pow]
              field_simp
            have h7 : ((4 : ℝ)⁻¹) ^ k = ((4 : ℝ) ^ k)⁻¹ := inv_pow _ _
            have h8 : (((4 : ℝ) ^ k)⁻¹) ^ t ≤ 1 :=
              pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hq)
            have h6 : (0 : ℝ) < ((4 : ℝ) ^ k)⁻¹ := by positivity
            rw [e, h7]
            exact mul_le_of_le_one_right h6.le h8
          simp only [hc]
          calc (4 : ℝ) ^ s * (((4 : ℝ) ^ k)⁻¹) ^ s * (C' * ((4 : ℝ) ^ k) ^ d)
              = (4 : ℝ) ^ s * C' * ((((4 : ℝ) ^ k)⁻¹) ^ s * ((4 : ℝ) ^ k) ^ d) := by ring
            _ ≤ _ := by gcongr
  have hsum : Summable fun k : ℕ => (4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ∫⁻ x, ENNReal.ofReal (((1 + h x)⁻¹) ^ s) ∂μ
      ≤ ∫⁻ x, ∑' k, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x ∂μ :=
        lintegral_mono point
    _ = ∑' k, ∫⁻ x, (A k).indicator (fun _ => ENNReal.ofReal (c k)) x ∂μ :=
        lintegral_tsum fun k => (measurable_const.indicator (hAm k)).aemeasurable
    _ = ∑' k, ENNReal.ofReal (c k) * μ (A k) := by
        congr 1; funext k
        rw [lintegral_indicator (hAm k), setLIntegral_const]
    _ ≤ ∑' k, ENNReal.ofReal ((4 : ℝ) ^ s * C' * ((4 : ℝ)⁻¹) ^ k) :=
        ENNReal.tsum_le_tsum hterm
    _ < ⊤ := hsum.tsum_ofReal_lt_top

theorem one_add_hs_inv_pow_lintegral_lt_top : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
    ∫⁻ g, ENNReal.ofReal (((1 + hs (umat g))⁻¹) ^ s) ∂(muG ε) < ⊤ := by
  intro n ε
  obtain ⟨C, hC⟩ := muG_hs_ball_le n ε
  refine ⟨n ^ 2 + 1, fun s hs' => ?_⟩
  refine lintegral_one_add_inv_pow_lt_top (muG ε) (fun g => hs (umat g))
    (continuous_hs_umat ε).measurable (fun g => ?_) (n ^ 2) C (fun k => ?_) s hs'
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  · have e : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h1 := hC ((2 : ℝ) ^ k) (one_le_pow₀ (by norm_num))
    have e2 : ((2 : ℝ) ^ k) ^ (2 * n ^ 2) = ((4 : ℝ) ^ k) ^ n ^ 2 := by
      rw [e]; exact pow_mul _ 2 (n ^ 2)
    rw [e2, ← e] at h1
    exact h1

end GlobalTheory.CompanionTheory.HolPQ
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.RpowNegLeOfDichotomy

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume

open MeasureTheory

theorem wt_eq_hs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : wt M = Formalism.REAL.hs M := by
  have key : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    have h : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold wt Formalism.REAL.hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, key]
  exact Finset.sum_comm

theorem one_le_hs_of_inUJ {n : ℕ} (hn : 0 < n) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ)
    (h : Formalism.REAL.inUJ ε g) : 1 ≤ Formalism.REAL.hs g := by
  set a : Fin n := ⟨0, hn⟩ with ha
  have hs1 : ∀ k : Fin n, ‖(if ε k = true then (1 : ℂ) else -1)‖ = 1 := by
    intro k; split_ifs <;> simp
  have e : ∑ k, star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a =
      (if ε a = true then (1 : ℂ) else -1) := by
    have h2 := congrFun (congrFun h a) a
    simpa [Formalism.REAL.Jm, Matrix.mul_apply, Matrix.mul_diagonal, Matrix.diagonal_apply] using h2
  have h3 : (1 : ℝ) ≤ ∑ k, ‖g k a‖ ^ 2 := by
    calc (1 : ℝ) = ‖∑ k, star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a‖ := by
          rw [e, hs1]
      _ ≤ ∑ k, ‖star (g k a) * (if ε k = true then (1 : ℂ) else -1) * g k a‖ := norm_sum_le _ _
      _ = ∑ k, ‖g k a‖ ^ 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul, hs1, norm_star]; ring
  refine h3.trans ?_
  unfold Formalism.REAL.hs
  refine Finset.sum_le_sum fun k _ => ?_
  exact Finset.single_le_sum (f := fun j => ‖g k j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ a)

theorem rpow_neg_le_of_dichotomy {w b' : ℝ} {s : ℕ} (hw : w = 0 ∨ 1 ≤ w) (hb : (s : ℝ) ≤ b') :
    w ^ (-b') ≤ ((2 : ℝ) ^ b' + 1) * ((1 + w)⁻¹) ^ s := by
  have hb0 : 0 ≤ b' := (Nat.cast_nonneg s).trans hb
  have h2 : (0 : ℝ) < (2 : ℝ) ^ b' := Real.rpow_pos_of_pos (by norm_num) _
  rcases hw with rfl | hw
  · have h1 : (0 : ℝ) ^ (-b') ≤ 1 := Real.zero_rpow_le_one _
    simp only [add_zero, inv_one, one_pow, mul_one]
    linarith
  · have hw0 : 0 < w := by linarith
    have hu0 : 0 < (1 + w)⁻¹ := by positivity
    have hu1 : (1 + w)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hwi : w⁻¹ ≤ 2 * (1 + w)⁻¹ := by
      rw [inv_le_comm₀ hw0 (by positivity), mul_inv, inv_inv]
      linarith
    calc w ^ (-b') = (w⁻¹) ^ b' := by rw [Real.rpow_neg hw0.le, Real.inv_rpow hw0.le]
      _ ≤ (2 * (1 + w)⁻¹) ^ b' := Real.rpow_le_rpow (by positivity) hwi hb0
      _ = (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ b' := Real.mul_rpow (by norm_num) hu0.le
      _ ≤ (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ (s : ℝ) := by
          gcongr ?_ * ?_
          exact Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hb
      _ = (2 : ℝ) ^ b' * ((1 + w)⁻¹) ^ s := by rw [Real.rpow_natCast]
      _ ≤ _ := by
          have : 0 ≤ ((1 + w)⁻¹) ^ s := by positivity
          nlinarith

theorem integrable_wt_rpow_neg {n : ℕ} (ε : Fin n → Bool) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ b' : ℝ, b ≤ b' →
      MeasureTheory.Integrable (fun g : UJ ε => wt (uMat g) ^ (-b')) (Formalism.REAL.muG ε).inv := by
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.HolPQ.one_add_hs_inv_pow_lintegral_lt_top n ε
  have hfin : ∫⁻ g : UJ ε, ENNReal.ofReal (((1 + Formalism.REAL.hs (uMat g))⁻¹) ^ s) ∂(Formalism.REAL.muG ε) < ⊤ :=
    hs s le_rfl
  refine ⟨s, Nat.cast_nonneg s, fun b' hb' => ?_⟩
  have hinv : (Formalism.REAL.muG ε).inv = Formalism.REAL.muG ε := Formalism.REAL.invInvariant n ε
  rw [hinv]
  have hc : Continuous fun g : UJ ε => Formalism.REAL.hs (uMat g) := GlobalTheory.CompanionTheory.HolPQ.continuous_hs_umat ε
  have hnn : ∀ g : UJ ε, 0 ≤ Formalism.REAL.hs (uMat g) := fun g =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hI : Integrable (fun g : UJ ε => ((1 + Formalism.REAL.hs (uMat g))⁻¹) ^ s) (Formalism.REAL.muG ε) := by
    refine ⟨((measurable_const.add hc.measurable).inv.pow_const s).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => by
      have := hnn g
      positivity)]
    exact hfin
  have hw : ∀ g : UJ ε, wt (uMat g) = Formalism.REAL.hs (uMat g) := fun g => wt_eq_hs _
  have hmeas : Measurable fun g : UJ ε => wt (uMat g) ^ (-b') := by
    simp only [hw]
    exact hc.measurable.pow_const _
  refine (hI.const_mul ((2 : ℝ) ^ b' + 1)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  have hdich : Formalism.REAL.hs (uMat g) = 0 ∨ 1 ≤ Formalism.REAL.hs (uMat g) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · left; simp [Formalism.REAL.hs]
    · right; exact one_le_hs_of_inUJ hn ε _ g.2
  rw [hw, Real.norm_of_nonneg (Real.rpow_nonneg (hnn g) _)]
  exact rpow_neg_le_of_dichotomy hdich hb'

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Volume

end
end
end
