module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTiltUntiltLeOfFrobeniusSeriesSizeLeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobeniusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLawsStatement
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLawsStatement
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOverPadicOfIndepModPrime

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem indep_over_Ql_of_indep_mod_l : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  intro l _ d ι w γ hw hn c hc
  by_contra hne
  obtain ⟨a1, ha1⟩ := Function.ne_iff.mp hne
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ (fun a => ‖c a‖) ⟨a1, Finset.mem_univ _⟩
  have hc0 : c a₀ ≠ 0 := by
    intro h
    have := ha₀ a1 (Finset.mem_univ _)
    simp only [h, norm_zero] at this
    exact ha1 (norm_le_zero_iff.mp this)
  set c' : Fin d → ℚ_[l] := fun a => c a / c a₀ with hc'
  have hc'le : ∀ a, ‖c' a‖ ≤ 1 := by
    intro a
    simp only [hc', norm_div]
    exact div_le_one_of_le₀ (ha₀ a (Finset.mem_univ _)) (norm_nonneg _)
  have hc'a₀ : c' a₀ = 1 := div_self hc0
  have hsum' : ∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i = 0 := by
    intro i
    have : ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i
        = algebraMap ℚ_[l] ℂ_[l] (c a₀)⁻¹ * ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hc', div_eq_mul_inv, map_mul]
      ring
    rw [this, hc i, mul_zero]
  let e : Fin d → ℤ_[l] := fun a => ⟨c' a, hc'le a⟩
  let n : Fin d → ℕ := fun a => (e a).appr 1
  have hen : ∀ a, ‖e a - (n a : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
    intro a
    have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (by simpa using PadicInt.appr_spec 1 (e a))
    simpa using h
  have hlC : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have hsmall : ∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i := by
    intro i
    have heq : ∑ a, (n a : ℂ_[l]) * w a i
        = ∑ a, ((n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)) * w a i := by
      simp only [sub_mul, Finset.sum_sub_distrib, hsum' i, sub_zero]
    rw [heq, hlC]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    · exact mul_nonneg (by positivity) ((norm_nonneg _).trans (hw a₀ i))
    · intro a _
      rw [norm_mul]
      refine mul_le_mul ?_ (hw a i) (norm_nonneg _) (by positivity)
      have : (n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)
          = algebraMap ℚ_[l] ℂ_[l] (-(((e a - (n a : ℤ_[l]) : ℤ_[l]) : ℚ_[l]))) := by
        have hea : ((e a : ℤ_[l]) : ℚ_[l]) = c' a := rfl
        rw [map_neg, PadicInt.coe_sub, PadicInt.coe_natCast, hea, map_sub, map_natCast]
        ring
      rw [this, norm_algebraMap', norm_neg, PadicInt.padic_norm_e_of_padicInt]
      exact hen a
  have hdiv := hn n hsmall a₀
  have hlt : ‖(n a₀ : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]
    obtain ⟨k, hk⟩ := hdiv
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  have he1 : ‖e a₀‖ = 1 := by
    show ‖c' a₀‖ = 1
    rw [hc'a₀, norm_one]
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have : ‖e a₀‖ ≤ max ‖e a₀ - (n a₀ : ℤ_[l])‖ ‖(n a₀ : ℤ_[l])‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (e a₀ - (n a₀ : ℤ_[l])) (n a₀ : ℤ_[l])
  rw [he1] at this
  have := this.trans_lt (max_lt ((hen a₀).trans_lt hlinv) hlt)
  exact lt_irrefl _ this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOverPadicOfIndepModPrimeStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.indep_over_padic_of_indep_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  first | exact @GlobalTheory.indep_over_Ql_of_indep_mod_l | exact GlobalTheory.indep_over_Ql_of_indep_mod_l | (intros; apply GlobalTheory.indep_over_Ql_of_indep_mod_l <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesAddSubLe

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem lam_add_sub_le : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x y : Fl l), 1 ≤ h → r < 1 → ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖lam h j (x + y) - lam h j x - lam h j y‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  intro l _ h j r x y hh hr hx hy
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hx
  have hxy : ‖sh (x + y)‖ ≤ r := (GlobalTheory.T.tiltUntilt_add_estimate_le l r x y hx hy).2
  have sx := (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r x hh hr hx).1
  have sy := (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r y hh hr hy).1
  have sxy := (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r (x + y) hh hr hxy).1
  have hs := (sxy.sub sx).sub sy
  have hg := (GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r hh hr0 hr).1
  have hpw := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  have hε : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r hh hr0 hr).2.2.1
  have key := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℤ _ _ ∅ _ hε hs (by
    intro n _
    set k : ℤ := n * h + j
    beta_reduce
    rw [hpw.1 k x y]
    have e : (l : ℂ_[l]) ^ (-n) * sh (pw k x + pw k y) - (l : ℂ_[l]) ^ (-n) * sh (pw k x)
        - (l : ℂ_[l]) ^ (-n) * sh (pw k y)
        = (l : ℂ_[l]) ^ (-n) * (sh (pw k x + pw k y) - sh (pw k x) - sh (pw k y)) := by ring
    rw [e, norm_mul, norm_zpow]
    have hl0 : 0 ≤ (l : ℝ) ^ k := zpow_nonneg (Nat.cast_nonneg _) _
    have bx : ‖sh (pw k x)‖ ≤ r ^ ((l : ℝ) ^ k) := by
      rw [hpw.2.2.2.2.2.2 k x]; exact Real.rpow_le_rpow (norm_nonneg _) hx hl0
    have by' : ‖sh (pw k y)‖ ≤ r ^ ((l : ℝ) ^ k) := by
      rw [hpw.2.2.2.2.2.2 k y]; exact Real.rpow_le_rpow (norm_nonneg _) hy hl0
    have ha := (GlobalTheory.T.tiltUntilt_add_estimate_le l _ (pw k x) (pw k y) bx by').1
    have hn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (-n) := zpow_nonneg (norm_nonneg _) _
    calc ‖(l : ℂ_[l])‖ ^ (-n) * ‖sh (pw k x + pw k y) - sh (pw k x) - sh (pw k y)‖
        ≤ ‖(l : ℂ_[l])‖ ^ (-n) * (‖(l : ℂ_[l])‖ * r ^ ((l : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left ha hn
      _ = ‖(l : ℂ_[l])‖ * (‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ k)) := by ring
      _ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := mul_le_mul_of_nonneg_left (hg n) (norm_nonneg _))
  simpa using key

end GlobalTheory.PSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesAddSubLeStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_add_sub_le : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x y : Fl l), 1 ≤ h → r < 1 → ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖lam h j (x + y) - lam h j x - lam h j y‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  first | exact @GlobalTheory.PSer.lam_add_sub_le | exact GlobalTheory.PSer.lam_add_sub_le | (intros; apply GlobalTheory.PSer.lam_add_sub_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesNatCombinationApprox

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem untiltFrobeniusLaurentSeries_zero (l : ℕ) [Fact l.Prime] (h j : ℕ) : lam h j (0 : Fl l) = 0 := by
  unfold lam
  have h0 : ∀ n : ℤ, (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) (0 : Fl l)) = 0 := by
    intro n
    rw [(GlobalTheory.T.tiltFrobeniusIntegerPower_laws l).2.2.1, (GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.1, mul_zero]
  simp only [h0, tsum_zero]

theorem norm_add_three_le {l : ℕ} [Fact l.Prime] (a b c : ℂ_[l]) (C : ℝ)
    (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) (hc : ‖c‖ ≤ C) : ‖a + b + c‖ ≤ C := by
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hc)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem untiltFrobeniusLaurentSeries_nsmul_approx (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x : Fl l)
    (hh : 1 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : ‖sh x‖ ≤ r) (m : ℕ) :
    ‖sh (m • x)‖ ≤ r ∧ ‖lam h j (m • x) - (m : ℂ_[l]) * lam h j x‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  have hC : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r hh hr0 hr1).2.2.1
  induction m with
  | zero =>
    simp only [zero_smul, Nat.cast_zero, zero_mul, sub_zero, untiltFrobeniusLaurentSeries_zero, norm_zero, (GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.1]
    exact ⟨hr0, hC⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [succ_nsmul]
    obtain ⟨hadd, hsh⟩ := GlobalTheory.T.tiltUntilt_add_estimate_le l r (m • x) x ih1 hx
    refine ⟨hsh, ?_⟩
    have hl := GlobalTheory.T.untiltFrobeniusLaurentSeries_add_sub_le l h j r (m • x) x hh hr1 ih1 hx
    have heq : lam h j (m • x + x) - ((m + 1 : ℕ) : ℂ_[l]) * lam h j x =
        (lam h j (m • x + x) - lam h j (m • x) - lam h j x) + (lam h j (m • x) - (m : ℂ_[l]) * lam h j x) + 0 := by
      push_cast; ring
    rw [heq]
    exact norm_add_three_le _ _ _ _ hl ih2 (by simpa using hC)

theorem untiltFrobeniusLaurentSeries_finset_sum_approx (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) {ι : Type*} [DecidableEq ι]
    (x : ι → Fl l) (n : ι → ℕ)
    (hh : 1 ≤ h) (hr0 : 0 ≤ r) (hr1 : r < 1) (hx : ∀ a, ‖sh (x a)‖ ≤ r) (s : Finset ι) :
    ‖sh (∑ a ∈ s, n a • x a)‖ ≤ r ∧
      ‖lam h j (∑ a ∈ s, n a • x a) - ∑ a ∈ s, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  have hC : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r hh hr0 hr1).2.2.1
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, untiltFrobeniusLaurentSeries_zero, sub_zero, norm_zero, (GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l).2.1]
    exact ⟨hr0, hC⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨hu1, hu2⟩ := untiltFrobeniusLaurentSeries_nsmul_approx l h j r (x a) hh hr0 hr1 (hx a) (n a)
    obtain ⟨hadd, hsh⟩ := GlobalTheory.T.tiltUntilt_add_estimate_le l r (n a • x a) (∑ b ∈ s, n b • x b) hu1 ih1
    refine ⟨hsh, ?_⟩
    have hl := GlobalTheory.T.untiltFrobeniusLaurentSeries_add_sub_le l h j r (n a • x a) (∑ b ∈ s, n b • x b) hh hr1 hu1 ih1
    have heq : lam h j (n a • x a + ∑ b ∈ s, n b • x b) -
        ((n a : ℂ_[l]) * lam h j (x a) + ∑ b ∈ s, (n b : ℂ_[l]) * lam h j (x b)) =
        (lam h j (n a • x a + ∑ b ∈ s, n b • x b) - lam h j (n a • x a) - lam h j (∑ b ∈ s, n b • x b)) +
        (lam h j (n a • x a) - (n a : ℂ_[l]) * lam h j (x a)) +
        (lam h j (∑ b ∈ s, n b • x b) - ∑ b ∈ s, (n b : ℂ_[l]) * lam h j (x b)) := by ring
    rw [heq]
    exact norm_add_three_le _ _ _ _ hl hu2 ih2

theorem lamsum : ∀ (l : ℕ) [Fact l.Prime] (h j d : ℕ) (r : ℝ) (x : Fin d → Fl l) (n : Fin d → ℕ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ a, ‖sh (x a)‖ ≤ r) → ‖sh (∑ a, n a • x a)‖ ≤ r ∧ ‖lam h j (∑ a, n a • x a) - ∑ a, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  intro l _ h j d r x n hh hr0 hr1 hx
  exact untiltFrobeniusLaurentSeries_finset_sum_approx l h j r x n hh hr0 hr1 hx Finset.univ

end GlobalTheory.PSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesNatCombinationApproxStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.untiltFrobeniusLaurentSeries_natCombination_approx : ∀ (l : ℕ) [Fact l.Prime] (h j d : ℕ) (r : ℝ) (x : Fin d → Fl l) (n : Fin d → ℕ), 1 ≤ h → 0 ≤ r → r < 1 → (∀ a, ‖sh (x a)‖ ≤ r) → ‖sh (∑ a, n a • x a)‖ ≤ r ∧ ‖lam h j (∑ a, n a • x a) - ∑ a, (n a : ℂ_[l]) * lam h j (x a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  first | exact @GlobalTheory.PSer.lamsum | exact GlobalTheory.PSer.lamsum | (intros; apply GlobalTheory.PSer.lamsum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesLinearIndependentOfFirstTer

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_indep_of_first_terms : ∀ (l : ℕ) [Fact l.Prime] (h d : ℕ) (r : ℝ) (y : Fin d → ℕ → Fl l), 2 ≤ h → 0 ≤ r → r < 1 → (∀ a k, ‖sh (y a k)‖ ≤ r) → (∀ n : Fin d → ℕ, ‖sh (∑ a, n a • y a 0)‖ ≤ r ^ l ^ h → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  intro l _ h d r y hh hr0 hr1 hy hdet c hc
  have h1 : 1 ≤ h := by omega
  refine GlobalTheory.T.indep_over_padic_of_indep_mod_prime l d (Fin 2) (fun a i => abelian₂ h i (y a)) (fun i => gam l h i r) ?_ ?_ c ?_
  · intro a i
    exact (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h i r (y a) h1 hr1 (hy a)).2.2.1
  · intro n hn
    apply hdet n
    have hls := fun j => GlobalTheory.T.untiltFrobeniusLaurentSeries_natCombination_approx l h j d r (fun a => y a 0) n h1 hr0 hr1 (fun a => hy a 0)
    have hρ0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hρ1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (pow_pos (Fact.out : l.Prime).pos h).ne'
    refine GlobalTheory.T.norm_tiltUntilt_le_of_frobeniusSeries_size_le l h (r ^ l ^ h) (∑ a, n a • y a 0) hh hρ0 hρ1 (lt_of_le_of_lt (hls 0).1 hr1) ?_
    intro j hj
    have hG := GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r h1 hr0 hr1
    rw [hG.2.2.2.2.1]
    have hnn : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r := mul_nonneg (norm_nonneg _) hG.2.2.1
    have hA := (hls j).2
    have hB : ‖∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a))‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hnn fun a _ => ?_
      rw [norm_mul]
      have hb := (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h j r (y a) h1 hr1 (hy a)).2.1
      rw [norm_sub_rev] at hb
      calc ‖(n a : ℂ_[l])‖ * ‖lam h j (y a 0) - abelian₂ h j (y a)‖ ≤ 1 * (‖(l : ℂ_[l])‖ * gam l h j r) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) hb (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hC : ‖∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := hn ⟨j, hj⟩
    have heq : lam h j (∑ a, n a • y a 0) = (lam h j (∑ a, n a • y a 0) - ∑ a, (n a : ℂ_[l]) * lam h j (y a 0)) + (∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a)) + ∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hB hC)
  · intro i
    exact hc i.1 i.2

end GlobalTheory.PSer
end
end
