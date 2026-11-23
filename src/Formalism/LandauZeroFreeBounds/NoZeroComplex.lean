module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Lemma
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.NoZeroComplexOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivReal
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf
import Formalism.ZeroFreeRegion.FinalZFR

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZeroExpansionWithMultiplicity

section

@[expose] public section

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem localZeroExpansionWithMultiplicity : LandauLocal2 := by
  intro f z₀ r M hr hM hf hfz₀ hbound
  obtain ⟨Z, m, h1, h2, h3, -, h5, h6⟩ := exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound
  exact ⟨Z, m, h1, h2, h3, h5, h6⟩

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZerosOf

section

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_sub_le_re_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : z₀.re - r ≤ w.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h1 := Complex.abs_re_le_norm (w - z₀)
  have h2 := neg_abs_le (w - z₀).re
  rw [Complex.sub_re] at h1 h2
  linarith

lemma norm_le_norm_add_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : ‖w‖ ≤ ‖z₀‖ + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  calc ‖w‖ = ‖z₀ + (w - z₀)‖ := by rw [add_sub_cancel]
    _ ≤ ‖z₀‖ + ‖w - z₀‖ := norm_add_le _ _
    _ ≤ ‖z₀‖ + r := by linarith

lemma norm_center_le (t : ℝ) : ‖(11 / 10 : ℂ) + t * I‖ ≤ 11 / 10 + |t| := by
  have h1 : ‖(11 / 10 : ℂ)‖ = 11 / 10 := by
    rw [show (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(11 / 10 : ℂ) + t * I‖ ≤ ‖(11 / 10 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = 11 / 10 + |t| := by rw [h1, h2]

lemma re_sum_div_sub (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)).re = ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (z - ρ)).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [div_eq_mul_one_div, show ((m ρ : ℕ) : ℂ) = ((m ρ : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]

lemma log_le_div_log_two_mul (C₁ L : ℝ) (hC₁ : 1 ≤ C₁) (hL : Real.log 2 ≤ L) :
    Real.log (22 * C₁) ≤ Real.log (22 * C₁) / Real.log 2 * L := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 ≤ Real.log (22 * C₁) := Real.log_nonneg (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  exact mul_le_mul_of_nonneg_left hL ha

theorem localZeroSumBoundOfBounds : LocalZerosOf := by
  intro hLan hGr hInv
  obtain ⟨C, hC⟩ := hGr
  set C₁ : ℝ := max C 1 with hC₁def
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  have hCC : C ≤ C₁ := le_max_left _ _
  refine ⟨120 * (1 + Real.log (22 * C₁) / Real.log 2), ?_⟩
  intro q _ χ hχ t
  set z₀ : ℂ := (11 / 10 : ℂ) + t * I with hz₀
  have hz₀re : z₀.re = 11 / 10 := by
    rw [hz₀, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]
    norm_num
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have ht0 : 0 ≤ |t| := abs_nonneg t
  set M : ℝ := 22 * C₁ * q * (|t| + 2) with hM
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ C₁ * q := by nlinarith
    nlinarith
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall z₀ (3 / 5)) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hnz : ∀ s : ℂ, 1 < s.re → DirichletCharacter.LFunction χ s ≠ 0 := fun s hs =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 := hnz z₀ (by rw [hz₀re]; norm_num)
  have hlow : 1 / 11 ≤ ‖DirichletCharacter.LFunction χ z₀‖ := by
    have h := hInv q χ z₀ (by rw [hz₀re]; norm_num)
    rw [hz₀re, show (11 / 10 : ℝ) / (11 / 10 - 1) = 11 by norm_num] at h
    have hpos : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    rw [inv_le_comm₀ hpos (by norm_num)] at h
    calc (1 / 11 : ℝ) = (11 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := h
  have hbound : ∀ z ∈ Metric.closedBall z₀ (3 / 5),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre : 1 / 2 ≤ z.re := by
      have := re_sub_le_re_of_mem_closedBall hz
      rw [hz₀re] at this
      linarith
    have h1 := hC q χ hχ z hre
    have hn : ‖z‖ ≤ 11 / 10 + |t| + 3 / 5 := by
      have := norm_le_norm_add_of_mem_closedBall hz
      have := norm_center_le t
      linarith
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ C₁ * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hq0) (by linarith)
      _ ≤ C₁ * q * (2 * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hq0)
      _ = M * (1 / 11) := by rw [hM]; ring
      _ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := mul_le_mul_of_nonneg_left hlow (by linarith)
  obtain ⟨Z, m, hZ, hm1, hm2, -, happrox⟩ :=
    hLan (DirichletCharacter.LFunction χ) z₀ (3 / 5) M (by norm_num) hM1 hdiff hf0 hbound
  refine ⟨Z, m, ?_, hm1, hm2, ?_⟩
  · intro ρ
    rw [hZ ρ, show (3 / 5 : ℝ) / 3 = 1 / 5 by norm_num]
  · intro σ hσ1 hσ2
    set s : ℂ := (σ : ℂ) + t * I with hs
    have hsre : s.re = σ := by
      rw [hs, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]
    have hsball : s ∈ Metric.closedBall z₀ ((3 / 5) / 6) := by
      rw [Metric.mem_closedBall, dist_eq_norm, show (3 / 5 : ℝ) / 6 = 1 / 10 by norm_num]
      have hd : s - z₀ = ((σ - 11 / 10 : ℝ) : ℂ) := by
        rw [hs, hz₀]
        push_cast
        ring
      rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := hnz s (by rw [hsre]; exact hσ1)
    have hA := happrox s hsball hfs
    have hpos1 : 0 < 22 * C₁ := by linarith
    have hpos2 : 0 < (q : ℝ) * (|t| + 2) := by positivity
    have hL : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hlogM : Real.log M ≤
        (1 + Real.log (22 * C₁) / Real.log 2) * Real.log ((q : ℝ) * (|t| + 2)) := by
      have hMe : M = (22 * C₁) * ((q : ℝ) * (|t| + 2)) := by rw [hM]; ring
      rw [hMe, Real.log_mul hpos1.ne' hpos2.ne']
      have := log_le_div_log_two_mul C₁ _ hC₁ hL
      nlinarith
    have hre := Complex.abs_re_le_norm
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
    have hre' := neg_abs_le
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re
    rw [Complex.sub_re, re_sum_div_sub] at hre hre'
    have h72 : 72 * Real.log M / (3 / 5) = 120 * Real.log M := by ring
    rw [h72] at hA
    have hneg : (negLD χ s).re =
        -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s).re := by
      rw [negLD, Complex.neg_re]
    rw [hneg]
    nlinarith

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf

section

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_le_natCast (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

lemma log_two_le_log_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq := one_le_natCast q
  apply Real.log_le_log (by norm_num)
  nlinarith [abs_nonneg t]

lemma log_mul_abs_add_two_pos (q : ℕ) [NeZero q] (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_mul_abs_add_two q t)

lemma inRegion_mono' {c c' : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (h : c ≤ c') (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at *
  have hL := log_mul_abs_add_two_pos q s.im
  have := div_le_div_of_nonneg_right h hL.le
  linarith

lemma re_pos_of_inRegion {c : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hc : c ≤ 1 / 2) (hs : InRegion c q s) :
    0 < s.re := by
  unfold InRegion at hs
  have hL := log_two_le_log_mul_abs_add_two q s.im
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := div_le_div_of_nonneg_right hc hLpos.le
  have h2 : (1 / 2 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 2) / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) h2pos hL
  have h3 : (1 / 2 : ℝ) / Real.log 2 < 1 := by
    rw [div_lt_one h2pos]; linarith [Real.log_two_gt_d9]
  linarith

lemma one_sub_div_log_le_re {c cz : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hcz : 0 < cz) (h : c ≤ cz)
    (hs : InRegion c q s) : 1 - cz / Real.log (|s.im| + 2) ≤ s.re := by
  unfold InRegion at hs
  have hq := one_le_natCast q
  have hT : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hlogT : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith)
  have hle : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h1 := div_le_div_of_nonneg_right h hLpos.le
  have h2 := div_le_div_of_nonneg_left hcz.le hlogT hle
  linarith

theorem zeroFreeRegionExceptionalZeroOfBounds : ZFRDirichletOf := by
  intro hZ hT hN hL hS h2
  obtain ⟨cz, hcz, hZ⟩ := hZ
  obtain ⟨cN, hcN, hN⟩ := hN
  obtain ⟨δ, cS, hδ, hcS, hS⟩ := hS
  obtain ⟨cL, hcL, hL⟩ := hL δ hδ
  obtain ⟨c2, hc2, h2⟩ := h2
  set c := min (min (min cz cN) (min cL cS)) (min c2 (1 / 2)) with hc
  have hc0 : 0 < c := lt_min (lt_min (lt_min hcz hcN) (lt_min hcL hcS)) (lt_min hc2 (by norm_num))
  have hccz : c ≤ cz := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hccN : c ≤ cN := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hccL : c ≤ cL := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccS : c ≤ cS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcc2 : c ≤ c2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc12 : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, ?_⟩
  intro q _ χ s hs hz

  have key : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), InRegion c q s → IsLZero χ s →
      χ ^ 2 = 1 ∧ χ ≠ 1 ∧ |s.im| < δ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    intro χ s hs hz
    obtain ⟨hne, h0⟩ := hz
    have hχ1 : χ ≠ 1 := by
      rintro rfl
      have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
      have hre := re_pos_of_inRegion hc12 hs
      exact hZ s hs1 (one_sub_div_log_le_re hcz hccz hs) (hT q s hre hs1 h0)
    have hsq : χ ^ 2 = 1 := by
      by_contra hsq
      exact hN q χ s hsq (inRegion_mono' hccN hs) h0
    refine ⟨hsq, hχ1, ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hL q χ s hsq hχ1 hlt (inRegion_mono' hccL hs) h0
  obtain ⟨hsq, hχ1, hsm⟩ := key χ s hs hz
  obtain ⟨him, hder, -⟩ := hS q χ hsq hχ1 s s hsm hsm (inRegion_mono' hccS hs)
    (inRegion_mono' hccS hs) hz.2 hz.2
  refine ⟨hsq, hχ1, him, hder, ?_⟩
  intro χ' s' hs' hz'
  obtain ⟨hsq', hχ1', hsm'⟩ := key χ' s' hs' hz'
  have him' := (hS q χ' hsq' hχ1' s' s' hsm' hsm' (inRegion_mono' hccS hs')
    (inRegion_mono' hccS hs') hz'.2 hz'.2).1
  have hχeq : χ' = χ := by
    by_contra hne
    have es : ((s.re : ℝ) : ℂ) = s := Complex.ext (by simp) (by simp [him])
    have es' : ((s'.re : ℝ) : ℂ) = s' := Complex.ext (by simp) (by simp [him'])
    have r1 : InRegion c2 q ((s.re : ℝ) : ℂ) := by rw [es]; exact inRegion_mono' hcc2 hs
    have r2 : InRegion c2 q ((s'.re : ℝ) : ℂ) := by rw [es']; exact inRegion_mono' hcc2 hs'
    rcases h2 q χ χ' hsq hsq' hχ1 hχ1' (Ne.symm hne) s.re s'.re r1 r2 with h | h
    · exact h (by rw [es]; exact hz.2)
    · exact h (by rw [es']; exact hz'.2)
  refine ⟨hχeq, ?_⟩
  rw [hχeq] at hz'
  exact (hS q χ hsq hχ1 s s' hsm hsm' (inRegion_mono' hccS hs) (inRegion_mono' hccS hs')
    hz.2 hz'.2).2.2

end Formalism.ZeroFreeDirichlet
end
end
end

-- Source module: Formalism.LandauZeroFreeBounds.NoZeroComplex

section

@[expose] public section

namespace Formalism.ZeroFreeDirichlet

theorem localZeros : LocalZeros :=
  localZeroSumBoundOfBounds localZeroExpansionWithMultiplicity lfunction_polynomial_growth inverseBound

theorem noZeroComplex : NoZeroComplex :=
  zeroFreeNonRealCharOfBounds localZeros l_log_deriv_right negLogDerivPositivity

theorem realLargeT : RealLargeT :=
  realCharZeroFreeLargeHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity trivial_log_deriv_bound

theorem realSmallT : RealSmallT :=
  realCharZeroSmallHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity realCharConj

theorem twoReal : TwoReal :=
  twoRealCharNoCommonZeroOfBounds localZeros l_log_deriv_right negLogDerivPositivity

theorem zFRDirichlet : ZFRDirichlet :=
  zeroFreeRegionExceptionalZeroOfBounds Formalism.ZF.zeroFreeRegion trivialCharZerosOfZeta noZeroComplex realLargeT realSmallT twoReal

end Formalism.ZeroFreeDirichlet
end
end
