module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Analysis.Normed.Group.Ultra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltFrobeniusIntegerPowerLawsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobeniusStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesRadiusSizeLawsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueMaxTermUntiltFrobeniusSeries

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.Uniq

theorem exists_strict_max (f d : ℤ → ℝ) (hd : ∀ n, f (n + 1) = f n + d n) (hanti : StrictAnti d)
    (hne : ∀ n, d n ≠ 0) (hpos : ∃ m, 0 < d m) (hneg : ∃ m, d m < 0) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → f n < f n₀ := by
  obtain ⟨m, hm⟩ := hpos
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, d z < 0 → b ≤ z := ⟨m, fun z hz => by
    by_contra hc
    push_neg at hc
    have := hanti hc
    linarith⟩
  obtain ⟨n₀, hn₀, hmin⟩ := Int.exists_least_of_bdd hbdd hneg
  have hafter : ∀ k, n₀ ≤ k → d k < 0 := fun k hk => by
    rcases hk.lt_or_eq with h | h
    · exact (hanti h).trans hn₀
    · rw [← h]; exact hn₀
  have hbefore : ∀ k, k < n₀ → 0 < d k := fun k hk => by
    rcases lt_or_gt_of_ne (hne k) with h | h
    · exact absurd (hmin k h) (not_le.2 hk)
    · exact h
  have hfwd : ∀ k : ℕ, f (n₀ + k + 1) < f n₀ := by
    intro k
    induction k with
    | zero =>
      have := hd n₀
      have := hafter n₀ le_rfl
      simp only [Nat.cast_zero, add_zero]
      linarith
    | succ k ih =>
      rw [show n₀ + ((k + 1 : ℕ) : ℤ) + 1 = n₀ + k + 1 + 1 by push_cast; ring]
      have := hd (n₀ + k + 1)
      have := hafter (n₀ + k + 1) (by omega)
      linarith
  have hbwd : ∀ k : ℕ, f (n₀ - k - 1) < f n₀ := by
    intro k
    induction k with
    | zero =>
      have := hd (n₀ - 1)
      have := hbefore (n₀ - 1) (by omega)
      simp only [Nat.cast_zero, sub_zero]
      rw [sub_add_cancel] at *
      linarith
    | succ k ih =>
      have := hd (n₀ - ((k + 1 : ℕ) : ℤ) - 1)
      have := hbefore (n₀ - ((k + 1 : ℕ) : ℤ) - 1) (by omega)
      rw [show n₀ - ((k + 1 : ℕ) : ℤ) - 1 + 1 = n₀ - k - 1 by push_cast; ring] at *
      linarith
  refine ⟨n₀, fun n hn => ?_⟩
  rcases lt_or_gt_of_ne hn with h | h
  · have := hbwd (n₀ - n - 1).toNat
    rwa [show n₀ - ((n₀ - n - 1).toNat : ℤ) - 1 = n by omega] at this
  · have := hfwd (n - n₀ - 1).toNat
    rwa [show n₀ + ((n - n₀ - 1).toNat : ℤ) + 1 = n by omega] at this

end GlobalTheory.PSer.Uniq

namespace GlobalTheory.PSer.Uniq

theorem exists_unique_max_term : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (s : ℝ), 2 ≤ h → 0 < s → s < 1 →
    ∃ j : ℕ, j < 2 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ →
      ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) <
        ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
  intro l _ h s hh hs0 hs1
  have hlp : l.Prime := Fact.out
  have hν1 : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hν0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hlp.ne_zero)
  set ν := ‖(l : ℂ_[l])‖ with hν
  have hL : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hL0 : (0 : ℝ) < l := by linarith
  have hls : Real.log s < 0 := Real.log_neg hs0 hs1
  have hlν : Real.log ν < 0 := Real.log_neg hν0 hν1
  have hq : (1 : ℝ) < (l : ℝ) ^ h := one_lt_pow₀ hL (by omega)
  set c : ℝ := ((l : ℝ) ^ h - 1) * Real.log s with hc_def
  have hc : c < 0 := mul_neg_of_pos_of_neg (by linarith) hls
  let u : ℕ → ℤ → ℝ := fun j n => (l : ℝ) ^ (n * h + j : ℤ)
  let f : ℕ → ℤ → ℝ := fun j n => -(n : ℝ) * Real.log ν + u j n * Real.log s
  let d : ℕ → ℤ → ℝ := fun j n => -Real.log ν + u j n * c
  have hu_succ : ∀ j n, u j (n + 1) = u j n * (l : ℝ) ^ h := fun j n => by
    simp only [u]
    rw [show ((n + 1) * (h : ℤ) + (j : ℤ)) = (n * h + j) + ((h : ℕ) : ℤ) by ring,
      zpow_add₀ hL0.ne', zpow_natCast]
  have hd : ∀ j n, f j (n + 1) = f j n + d j n := by
    intro j n
    simp only [f, d, hc_def]
    rw [hu_succ]
    push_cast
    ring
  have hmono : ∀ j, StrictMono (u j) := fun j a b hab => by
    simp only [u]
    apply zpow_lt_zpow_right₀ hL
    have : (0 : ℤ) < (b - a) * h := mul_pos (by omega) (by omega)
    linarith
  have hanti : ∀ j, StrictAnti (d j) := fun j a b hab => by
    simp only [d]
    have := mul_lt_mul_of_neg_right (hmono j hab) hc
    linarith
  set B : ℝ := Real.log ν / c with hB_def
  have hB : 0 < B := div_pos_of_neg_of_neg hlν hc
  have hBc : B * c = Real.log ν := div_mul_cancel₀ _ hc.ne
  have hpos : ∀ j, ∃ m, 0 < d j m := fun j => by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hB (inv_lt_one_of_one_lt₀ hL)
    refine ⟨-((k : ℤ) + j), ?_⟩
    have h1 : u j (-((k : ℤ) + j)) ≤ (l : ℝ) ^ (-(k : ℤ)) := by
      simp only [u]
      apply zpow_le_zpow_right₀ hL.le
      have : (0 : ℤ) ≤ ((k : ℤ) + j) * ((h : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
    have h2 : (l : ℝ) ^ (-(k : ℤ)) = ((l : ℝ)⁻¹) ^ k := by rw [zpow_neg, zpow_natCast, inv_pow]
    have h3 : u j (-((k : ℤ) + j)) < B := by rw [h2] at h1; exact h1.trans_lt hk
    have := mul_lt_mul_of_neg_right h3 hc
    simp only [d]
    linarith
  have hneg : ∀ j, ∃ m, d j m < 0 := fun j => by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt B hL
    refine ⟨k, ?_⟩
    have h1 : (l : ℝ) ^ ((k : ℤ)) ≤ u j k := by
      simp only [u]
      apply zpow_le_zpow_right₀ hL.le
      have : (0 : ℤ) ≤ (k : ℤ) * ((h : ℤ) - 1) := mul_nonneg (by omega) (by omega)
      nlinarith
    rw [zpow_natCast] at h1
    have := mul_lt_mul_of_neg_right (hk.trans_le h1) hc
    simp only [d]
    linarith
  have htie : ∀ n n', d 0 n = 0 → d 1 n' = 0 → False := by
    intro n n' h0 h1
    have e1 : u 0 n * c = u 1 n' * c := by simp only [d] at h0 h1; linarith
    have e2 := (zpow_right_strictMono₀ hL).injective (mul_right_cancel₀ hc.ne e1)
    push_cast at e2
    have hdvd : (h : ℤ) ∣ 1 := ⟨n - n', by linear_combination -e2⟩
    have := Int.eq_one_of_dvd_one (by positivity) hdvd
    omega
  have hfin : ∀ j, (∀ n, d j n ≠ 0) → ∃ n₀ : ℤ, ∀ n, n ≠ n₀ →
      ν ^ (-n) * s ^ (u j n) < ν ^ (-n₀) * s ^ (u j n₀) := by
    intro j hne
    obtain ⟨n₀, hn₀⟩ := exists_strict_max (f j) (d j) (hd j) (hanti j) hne (hpos j) (hneg j)
    refine ⟨n₀, fun n hn => ?_⟩
    have hT : ∀ m, Real.log (ν ^ (-m) * s ^ (u j m)) = f j m := fun m => by
      rw [Real.log_mul (zpow_pos hν0 _).ne' (Real.rpow_pos_of_pos hs0 _).ne', Real.log_zpow,
        Real.log_rpow hs0]
      simp only [f]
      push_cast
      ring
    rw [← Real.log_lt_log_iff (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _))
      (mul_pos (zpow_pos hν0 _) (Real.rpow_pos_of_pos hs0 _)), hT, hT]
    exact hn₀ n hn
  by_cases H : ∀ n, d 0 n ≠ 0
  · exact ⟨0, by norm_num, hfin 0 H⟩
  · push_neg at H
    obtain ⟨n, hn⟩ := H
    exact ⟨1, by norm_num, hfin 1 fun n' hn' => htie n n' hn hn'⟩

end GlobalTheory.PSer.Uniq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueMaxTermUntiltFrobeniusSeriesStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_unique_max_term_untiltFrobeniusSeries : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (s : ℝ), 2 ≤ h → 0 < s → s < 1 → ∃ j : ℕ, j < 2 ∧ ∃ n₀ : ℤ, ∀ n : ℤ, n ≠ n₀ → ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) < ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
  first | exact @GlobalTheory.PSer.Uniq.exists_unique_max_term | exact GlobalTheory.PSer.Uniq.exists_unique_max_term | (intros; apply GlobalTheory.PSer.Uniq.exists_unique_max_term <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormHasSumEqOfDominant

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem norm_hasSum_eq_of_dominant : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type)
    (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by
  intro K _ _ ι f s i₀ hsum h
  classical
  have hs : Summable f := hsum.summable
  have hf : Filter.Tendsto f Filter.cofinite (nhds 0) := hs.tendsto_cofinite_zero
  rw [← hsum.tsum_eq, hs.tsum_eq_add_tsum_ite i₀]
  by_cases h0 : f i₀ = 0
  · have : ∀ i, (if i = i₀ then 0 else f i) = 0 := by
      intro i
      split_ifs with hi
      · rfl
      · have := h i hi
        rw [h0, norm_zero] at this
        exact absurd this (norm_nonneg _).not_gt
    simp [this]
  have hc : 0 < ‖f i₀‖ := norm_pos_iff.2 h0
  set g : ι → K := fun i => if i = i₀ then 0 else f i with hg
  have hglt : ∀ i, ‖g i‖ < ‖f i₀‖ := by
    intro i
    simp only [hg]
    split_ifs with hi
    · simpa using hc
    · exact h i hi
  have hfin : {i | ¬ ‖f i‖ < ‖f i₀‖ / 2}.Finite := by
    have := (NormedAddGroup.tendsto_nhds_zero.1 hf) (‖f i₀‖ / 2) (by positivity)
    exact Filter.eventually_cofinite.1 this
  obtain ⟨j, -, hj⟩ := Set.exists_max_image _ (fun i => ‖g i‖) hfin
    ⟨i₀, by simp only [Set.mem_setOf_eq]; linarith⟩
  have hb : ‖∑' i, g i‖ ≤ max (‖f i₀‖ / 2) ‖g j‖ := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
    by_cases hi : ‖f i‖ < ‖f i₀‖ / 2
    · refine le_max_of_le_left ?_
      simp only [hg]
      split_ifs
      · simp only [norm_zero]; positivity
      · exact hi.le
    · exact le_max_of_le_right (hj i hi)
  have hlt : ‖∑' i, g i‖ < ‖f i₀‖ := hb.trans_lt (max_lt (by linarith) (hglt j))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormHasSumEqOfDominantStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by
  first | exact @GlobalTheory.norm_hasSum_eq_of_dominant | exact GlobalTheory.norm_hasSum_eq_of_dominant | (intros; apply GlobalTheory.norm_hasSum_eq_of_dominant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTiltUntiltLeOfFrobeniusSeriesSizeLe

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem norm_sh_le_of_lam_le : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (ρ : ℝ) (x : Fl l), 2 ≤ h → 0 ≤ ρ → ρ < 1 → ‖sh x‖ < 1 → (∀ j : ℕ, j < 2 → ‖lam h j x‖ ≤ gam l h j ρ) → ‖sh x‖ ≤ ρ := by
  intro l _ h ρ x h2 hρ0 hρ1 hs1 hlam
  by_contra hlt
  push_neg at hlt
  set s := ‖sh x‖ with hs
  have hs0 : 0 < s := lt_of_le_of_lt hρ0 hlt
  have h1 : 1 ≤ h := le_trans (by norm_num) h2
  obtain ⟨j, hj, n₀, hn₀⟩ := GlobalTheory.T.exists_unique_max_term_untiltFrobeniusSeries l h s h2 hs0 hs1
  obtain ⟨hsum, -, -, -⟩ := GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j s x h1 hs1 le_rfl
  have hpw := (GlobalTheory.T.tiltFrobeniusIntegerPower_laws l).2.2.2.2.2.2
  have hterm : ∀ n : ℤ, ‖(l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x)‖
      = ‖(l : ℂ_[l])‖ ^ (-n) * s ^ ((l : ℝ) ^ (n * h + j : ℤ)) := by
    intro n
    rw [norm_mul, norm_zpow, hpw]
  have hnorm : ‖lam h j x‖ = ‖(l : ℂ_[l])‖ ^ (-n₀) * s ^ ((l : ℝ) ^ (n₀ * h + j : ℤ)) := by
    rw [GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term ℂ_[l] ℤ _ _ n₀ hsum (by
      intro n hn
      rw [hterm, hterm]
      exact hn₀ n hn), hterm]
  obtain ⟨-, ⟨m, hm⟩, -, -, -, hmono⟩ := GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j s h1 hs0.le hs1
  have hgs : gam l h j s ≤ ‖lam h j x‖ := by
    rw [hm, hnorm]
    by_cases hmn : m = n₀
    · rw [hmn]
    · exact (hn₀ m hmn).le
  have hgρ : gam l h j ρ < gam l h j s := ((GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j ρ h1 hρ0 hρ1).2.2.2.2.2) s hlt hs1
  have := hlam j hj
  linarith

end GlobalTheory.PSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTiltUntiltLeOfFrobeniusSeriesSizeLeStatement

section

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_tiltUntilt_le_of_frobeniusSeries_size_le : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (ρ : ℝ) (x : Fl l), 2 ≤ h → 0 ≤ ρ → ρ < 1 → ‖sh x‖ < 1 → (∀ j : ℕ, j < 2 → ‖lam h j x‖ ≤ gam l h j ρ) → ‖sh x‖ ≤ ρ := by
  first | exact @GlobalTheory.PSer.norm_sh_le_of_lam_le | exact GlobalTheory.PSer.norm_sh_le_of_lam_le | (intros; apply GlobalTheory.PSer.norm_sh_le_of_lam_le <;> assumption)
end
end
