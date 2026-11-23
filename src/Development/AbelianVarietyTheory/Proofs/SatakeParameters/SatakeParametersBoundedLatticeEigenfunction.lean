module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorAlternatingSeriesIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NcardSublatticesOfIndexPrimePowerLeStatement
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfRecurrenceGrowth

section

@[expose] public section

open Finset

namespace GlobalTheory

theorem norm_le_of_recurrence_growth : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  intro β a C B m hB ha0 hrec hgrow b hb
  by_contra hlt
  push_neg at hlt
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; linarith
  set X : ℂ := b⁻¹ with hX
  have hXn : ‖X‖ = ‖b‖⁻¹ := norm_inv b
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set r : ℝ := B * ‖X‖ with hr
  have hrpos : 0 < r := by rw [hr, hXn]; positivity
  have hr1 : r < 1 := by
    rw [hr, hXn, ← div_eq_mul_inv, div_lt_one hbpos]; exact hlt
  have hes : ∀ k, Multiset.card β < k → β.esymm k = 0 := by
    intro k hk
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ hk]
  set d := Multiset.card β with hd
  set p : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * β.esymm k * X ^ k with hp
  have hpz : ∀ k ∉ Finset.range (d + 1), p k = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hp, hes k (by omega)]
  have hpsum : ∑ k ∈ Finset.range (d + 1), p k = 0 := by
    have h1 := congrArg (Polynomial.eval b) (Multiset.prod_X_sub_X_eq_sum_esymm β)
    rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at h1
    have hz : (Multiset.map (Polynomial.eval b)
        (Multiset.map (fun t => Polynomial.X - Polynomial.C t) β)).prod = 0 := by
      apply Multiset.prod_eq_zero
      rw [Multiset.map_map]
      exact Multiset.mem_map.mpr ⟨b, hb, by simp⟩
    rw [hz] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X] at h1
    have h2 : ∑ k ∈ Finset.range (d + 1), p k
        = X ^ d * ∑ j ∈ Finset.range (d + 1), (-1 : ℂ) ^ j * (β.esymm j * b ^ (d - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkd : k ≤ d := by rw [Finset.mem_range] at hk; omega
      have hXb : X ^ (d - k) * b ^ (d - k) = 1 := by
        rw [← mul_pow, hX, inv_mul_cancel₀ hb0, one_pow]
      have : X ^ d = X ^ k * X ^ (d - k) := by rw [← pow_add, Nat.add_sub_cancel' hkd]
      simp only [hp]
      rw [this]
      linear_combination (-1 : ℂ) ^ k * β.esymm k * X ^ k * hXb.symm
    rw [h2, ← h1, mul_zero]
  have hpsumm : Summable (fun k => ‖p k‖) :=
    summable_of_ne_finset_zero (s := Finset.range (d + 1)) (fun k hk => by simp [hpz k hk])
  have hptsum : ∑' k, p k = 0 := by
    rw [tsum_eq_sum (s := Finset.range (d + 1)) hpz, hpsum]
  set q : ℕ → ℂ := fun n => a n * X ^ n with hq
  have hgeo : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * r ^ n) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ m * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one m (by rw [Real.norm_eq_abs, abs_of_pos hrpos]; exact hr1)
    have h1 := (summable_nat_add_iff 1).mpr h0
    have h2 := h1.mul_left r⁻¹
    refine h2.congr (fun n => ?_)
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hqsumm : Summable (fun n => ‖q n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.mul_left C)
    simp only [hq, norm_mul, norm_pow]
    calc ‖a n‖ * ‖X‖ ^ n ≤ C * ((n : ℝ) + 1) ^ m * B ^ n * ‖X‖ ^ n :=
          mul_le_mul_of_nonneg_right (hgrow n) (by positivity)
      _ = C * (((n : ℝ) + 1) ^ m * r ^ n) := by rw [hr, mul_pow]; ring
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hpsumm hqsumm
  rw [hptsum, zero_mul] at hcauchy
  have hterm : ∀ n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k)
      = X ^ n * ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) := by
    intro n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by rw [Finset.mem_range] at hk; omega
    have : X ^ n = X ^ k * X ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    simp only [hp, hq]
    rw [this]; ring
  have hone : ∑' n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k) = 1 := by
    rw [tsum_eq_single 0]
    · simp [hp, hq, ha0, Multiset.esymm, Multiset.powersetCard_zero_left]
    · intro n hn
      rw [hterm n, hrec n (Nat.one_le_iff_ne_zero.mpr hn), mul_zero]
  rw [hone] at hcauchy
  exact zero_ne_one hcauchy

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfRecurrenceGrowthStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.norm_le_of_recurrence_growth' : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  first | exact @GlobalTheory.norm_le_of_recurrence_growth | exact GlobalTheory.norm_le_of_recurrence_growth | (intros; apply GlobalTheory.norm_le_of_recurrence_growth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeParametersBoundedLatticeEigenfunction

section

@[expose] public section

noncomputable section

namespace GlobalTheory.SatakeBound

open GlobalTheory.LatHecke

theorem esymm_map_mul (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (fun x => c * x)).esymm k = c ^ k * s.esymm k := by
  rw [Multiset.esymm, Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map,
    ← Multiset.sum_map_mul_left]
  congr 1
  apply Multiset.map_congr rfl
  intro t ht
  rw [Multiset.mem_powersetCard] at ht
  rw [Function.comp_apply]
  have := Multiset.prod_map_mul (m := t) (f := fun _ => c) (g := fun x => x)
  rw [this, Multiset.map_const', Multiset.prod_replicate, Multiset.map_id', ht.2]

noncomputable def recSeq (s : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => -∑ k ∈ Finset.range (n + 1), s (k + 1) * recSeq s (n - k)
decreasing_by all_goals omega

theorem cast_tri (k : ℕ) : (((k * (k - 1) / 2 : ℕ)) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rcases k with _ | j
  · simp
  · have h2 : 2 ∣ (j + 1) * j := by rw [mul_comm]; exact (Nat.even_mul_succ_self j).two_dvd
    rw [Nat.add_sub_cancel, Nat.cast_div h2 (by norm_num)]
    push_cast; ring

theorem main : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (φ : Lat O K r → E) (α : Multiset ℂ)
    (C : ℝ), α.card = r → φ ≠ 0 → (∀ L, ‖φ L‖ ≤ C) →
    (∀ k ≤ r, ∀ L, heckeElem k φ L =
      ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • φ L) →
    ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  intro O K _ _ _ _ _ _ _ r E _ _ φ α C hcard hφ hC hT x hx
  have hq1 : (1 : ℝ) < (qRes O : ℝ) := by exact_mod_cast one_lt_qRes (O := O)
  have hq0 : (0 : ℝ) < (qRes O : ℝ) := by linarith
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    rw [Multiset.card_eq_zero] at hcard
    subst hcard
    simp at hx
  obtain ⟨L0, hL0⟩ : ∃ L0, φ L0 ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    exact hφ (funext h)

  set d : ℕ → ℂ := fun k => if k ≤ r then
    (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k else 0 with hd_def
  have hd : ∀ k L, heckeElem k φ L = d k • φ L := by
    intro k L
    by_cases hk : k ≤ r
    · rw [hT k hk L, hd_def]; simp only [hk, if_true]
    · rw [heckeElem_eq_zero (by omega), hd_def]; simp only [hk, if_false, zero_smul]
  have hlin : ∀ (c : ℂ) k L, heckeElem k (fun M => c • φ M) L = (c * d k) • φ L := by
    intro c k L
    rw [heckeElem_eq_sum, ← Finset.smul_sum, ← heckeElem_eq_sum, hd, smul_smul]
  set s : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * (qRes O : ℂ) ^ (k * (k - 1) / 2) * d k with hs_def
  set a : ℕ → ℂ := recSeq s with ha_def

  have hA : ∀ n, heckeAll n φ = fun L => a n • φ L := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    rcases n with _ | m
    · funext L
      rw [heckeAll_zero, ha_def, recSeq, one_smul]
    · funext L
      have hid := GlobalTheory.T.heckeOperator_alternating_series_identity O K r E φ (m + 1) L (by omega)
      rw [Finset.sum_range_succ'] at hid
      have key : ∀ k ∈ Finset.range (m + 1),
          ((-1 : ℂ) ^ (k + 1) * (qRes O : ℂ) ^ ((k + 1) * (k + 1 - 1) / 2)) •
            heckeElem (k + 1) (heckeAll (m + 1 - (k + 1)) φ) L = (s (k + 1) * a (m - k)) • φ L := by
        intro k hk
        rw [show m + 1 - (k + 1) = m - k by omega, ih (m - k) (by omega), hlin, smul_smul]
        congr 1
        rw [hs_def]
        ring
      have h0 : ((-1 : ℂ) ^ 0 * (qRes O : ℂ) ^ (0 * (0 - 1) / 2)) = 1 := by simp
      rw [Finset.sum_congr rfl key, h0, one_smul, heckeElem_zero, ← Finset.sum_smul] at hid
      show heckeAll (m + 1) φ L = recSeq s (m + 1) • φ L
      rw [recSeq, neg_smul]
      exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hid)

  set c : ℝ := (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) with hc_def
  have hc0 : 0 < c := Real.rpow_pos_of_pos hq0 _
  set β : Multiset ℂ := α.map (fun y => (c : ℂ) * y) with hβ_def
  have hβs : ∀ k, (-1 : ℂ) ^ k * β.esymm k = s k := by
    intro k
    rw [hβ_def, esymm_map_mul, hs_def, hd_def]
    by_cases hk : k ≤ r
    · simp only [hk, if_true]
      have hreal : c ^ k = (qRes O : ℝ) ^ (k * (k - 1) / 2) *
          (qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) := by
        rw [hc_def, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_natCast (qRes O : ℝ),
          ← Real.rpow_add hq0, cast_tri]
        congr 1
        ring
      have hcomp : (c : ℂ) ^ k = (qRes O : ℂ) ^ (k * (k - 1) / 2) *
          (((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow, hreal, Complex.ofReal_mul, Complex.ofReal_pow,
          Complex.ofReal_natCast]
      rw [hcomp]
      ring
    · simp only [hk, if_false, mul_zero]
      rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [hcard]; omega)]
      simp
  have hrel : ∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [hβs]
    rw [Finset.sum_range_succ']
    have hs0 : s 0 = 1 := by
      rw [hs_def, hd_def]; simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    have ha1 : a (m + 1 - 0) = -∑ k ∈ Finset.range (m + 1), s (k + 1) * a (m - k) := by
      rw [Nat.sub_zero, ha_def, recSeq]
    rw [hs0, ha1]
    have : ∀ k ∈ Finset.range (m + 1), s (k + 1) * a (m + 1 - (k + 1)) = s (k + 1) * a (m - k) := by
      intro k _; rw [show m + 1 - (k + 1) = m - k by omega]
    rw [Finset.sum_congr rfl this]
    ring

  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC L0)
  have hnL0 : 0 < ‖φ L0‖ := norm_pos_iff.mpr hL0
  have hbound : ∀ n, ‖a n‖ ≤ (C / ‖φ L0‖) * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n := by
    intro n
    have h1 : ‖a n‖ * ‖φ L0‖ = ‖heckeAll n φ L0‖ := by
      rw [hA n, norm_smul]
    have h2 : ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C := by
      rw [heckeAll_eq_sum, Set.ncard_eq_toFinset_card _ (subIdx_finite n L0)]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun M _ => hC M).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 := GlobalTheory.T.ncard_sublatticesOfIndexPrimePower_le O K r n L0
    rw [show C / ‖φ L0‖ * ((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n =
        C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) / ‖φ L0‖ by ring,
      le_div_iff₀ hnL0, h1]
    calc ‖heckeAll n φ L0‖ ≤ (subIdx n L0).ncard * C := h2
      _ ≤ (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) * C :=
          mul_le_mul_of_nonneg_right h3 hC0
      _ = C * (((n : ℝ) + 1) ^ r * ((qRes O : ℝ) ^ (r - 1)) ^ n) := by ring
  have hB : 0 < (qRes O : ℝ) ^ (r - 1) := pow_pos hq0 _
  have hrec := GlobalTheory.T.norm_le_of_recurrence_growth' β a (C / ‖φ L0‖) ((qRes O : ℝ) ^ (r - 1)) r hB
    (by rw [ha_def, recSeq]) hrel hbound
  have hxb := hrec ((c : ℂ) * x) (Multiset.mem_map_of_mem _ hx)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at hxb
  have hcc : (qRes O : ℝ) ^ (r - 1) = c * c := by
    rw [hc_def, ← Real.rpow_add hq0, ← Real.rpow_natCast, Nat.cast_sub hr]
    congr 1
    push_cast
    ring
  rw [hcc] at hxb
  exact le_of_mul_le_mul_left hxb hc0

end GlobalTheory.SatakeBound
end
end
end
