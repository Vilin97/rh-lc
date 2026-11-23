module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Interval.Finset.Nat
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.LinearAlgebra.Vandermonde
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythree
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParsevalBoundIntegerVectorSmallFourierSupportStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.SeparationNumericalIneqCuspidalGLStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardNonregularResiduesModPowSubOneLe

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem card_nonregular_residues_le (q n : ℕ) (hq : 2 ≤ q) (hn : 0 < n) :
    ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤
      ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  classical
  have hsub : ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])) ⊆
      n.primeFactors.biUnion (fun p => (Finset.Ioo 0 (q ^ (n / p) - 1)).image
        (fun k => k * ((q ^ n - 1) / (q ^ (n / p) - 1)))) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Ioo] at hj
    obtain ⟨⟨hj0, hjN⟩, e, he, hje⟩ := hj
    rw [Finset.mem_Ioo] at he
    have hqe : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
    have h1 : q ^ n - 1 ∣ j * (q ^ e - 1) := by
      rw [Nat.mul_sub_one]
      exact (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_right j hqe)).1 hje.symm
    have h2 : q ^ n - 1 ∣ j * (q ^ Nat.gcd e n - 1) := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_mul_left]
      exact Nat.dvd_gcd h1 (Dvd.intro_left j rfl)
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_right e n
    have hglt : Nat.gcd e n < n := lt_of_le_of_lt (Nat.gcd_le_left n he.1) he.2
    have hm1 : m ≠ 1 := by
      rintro rfl
      omega
    obtain ⟨p, hp, r, hr⟩ := Nat.exists_prime_and_dvd hm1
    have hnp : n = p * (Nat.gcd e n * r) := by
      conv_lhs => rw [hm, hr]
      ring
    have hd : n / p = Nat.gcd e n * r := Nat.div_eq_of_eq_mul_right hp.pos hnp
    have hpn : p ∣ n := ⟨_, hnp⟩
    have hd0 : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos).ne'
    have h3 : q ^ n - 1 ∣ j * (q ^ (n / p) - 1) :=
      h2.trans (Nat.mul_dvd_mul_left j
        (Nat.pow_sub_one_dvd_pow_sub_one q ⟨r, hd⟩))
    have h4 : q ^ (n / p) - 1 ∣ q ^ n - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one q (Nat.div_dvd_of_dvd hpn)
    have hD : 0 < q ^ (n / p) - 1 := by
      have := Nat.one_lt_pow hd0 (show 1 < q by omega)
      omega
    obtain ⟨M, hM⟩ := h4
    rw [Finset.mem_biUnion]
    refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpn, hn.ne'⟩, ?_⟩
    rw [hM, mul_comm j] at h3
    obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left hD h3
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Ioo.2 ⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    · rw [hM, hk, mul_comm _ M] at hjN
      exact lt_of_mul_lt_mul_left hjN (Nat.zero_le _)
    · rw [hM, Nat.mul_div_cancel_left _ hD, hk, mul_comm]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine Finset.sum_le_sum fun p _ => Finset.card_image_le.trans ?_
  rw [Nat.card_Ioo]
  omega

end GlobalTheory.CuspGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardNonregularResiduesModPowSubOneLeStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le : ∀ q n : ℕ, 2 ≤ q → 0 < n → ((Finset.Ioo 0 (q ^ n - 1)).filter (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤ ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  first | exact @GlobalTheory.CuspGL.card_nonregular_residues_le | exact GlobalTheory.CuspGL.card_nonregular_residues_le | (intros; apply GlobalTheory.CuspGL.card_nonregular_residues_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormEightOfFourierVanishingOrderFifteen

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem no_norm_eight_of_fourier_vanishing_order_fifteen :
    ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 →
      (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  intro ω c hω hs hF
  have hinj : Function.Injective (fun j : Fin 15 => ω ^ (j : ℕ)) := by
    intro a b hab
    exact Fin.ext (hω.pow_inj a.2 b.2 hab)
  have hv : (fun i : Fin 15 => ((c ((i + 12) % 15) - c i : ℤ) : ℂ)) = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hinj
    intro j
    have h15 : (ω ^ (j : ℕ)) ^ 15 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hprod : ((ω ^ (j : ℕ)) ^ 3 - 1) *
        ∑ k ∈ Finset.range 15, (c k : ℂ) * (ω ^ (j : ℕ)) ^ k = 0 := by
      by_cases h5 : 5 ∣ (j : ℕ)
      · obtain ⟨m, hm⟩ := h5
        have : (ω ^ (j : ℕ)) ^ 3 = 1 := by
          rw [hm, ← pow_mul, show 5 * m * 3 = 15 * m by ring, pow_mul, hω.pow_eq_one, one_pow]
        rw [this, sub_self, zero_mul]
      · have := hF j j.2 h5
        simp only [pow_mul] at this
        rw [this, mul_zero]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (ω ^ (j : ℕ)) ^ i * ((c ((i + 12) % 15) - c i : ℤ) : ℂ)) 15]
    generalize ω ^ (j : ℕ) = x at h15 hprod
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hprod ⊢
    push_cast
    linear_combination hprod - ((c 12 : ℂ) + c 13 * x + c 14 * x ^ 2) * h15
  have hp : ∀ i : ℕ, i < 15 → c i = c ((i + 12) % 15) := by
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    simp only [Pi.zero_apply, Int.cast_eq_zero] at this
    linarith
  have h3 : c 3 = c 0 := hp 3 (by norm_num)
  have h4 : c 4 = c 1 := hp 4 (by norm_num)
  have h5 : c 5 = c 2 := hp 5 (by norm_num)
  have h6 : c 6 = c 3 := hp 6 (by norm_num)
  have h7 : c 7 = c 4 := hp 7 (by norm_num)
  have h8 : c 8 = c 5 := hp 8 (by norm_num)
  have h9 : c 9 = c 6 := hp 9 (by norm_num)
  have h10 : c 10 = c 7 := hp 10 (by norm_num)
  have h11 : c 11 = c 8 := hp 11 (by norm_num)
  have h12 : c 12 = c 9 := hp 12 (by norm_num)
  have h13 : c 13 = c 10 := hp 13 (by norm_num)
  have h14 : c 14 = c 11 := hp 14 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  rw [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3] at hs
  generalize c 0 ^ 2 = a at hs
  generalize c 1 ^ 2 = b at hs
  generalize c 2 ^ 2 = d at hs
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormEightOfFourierVanishingOrderFifteenStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 → (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | exact GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | (intros; apply GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythreeStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 → ∑ k ∈ Finset.range 63, c k ^ 2 = 12 → (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j → ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_twelve_order_sixtythree | exact GlobalTheory.no_norm_twelve_order_sixtythree | (intros; apply GlobalTheory.no_norm_twelve_order_sixtythree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.OrthogonalIntVectorsNotAgreeOnRegular

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

private lemma abs_sum_le_sum_sq_int (s : Finset ℕ) (a : ℕ → ℤ) :
    |∑ k ∈ s, a k| ≤ ∑ k ∈ s, a k ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rcases eq_or_ne (a k) 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |a k| := Int.one_le_abs h
    nlinarith [sq_abs (a k)]

theorem orthogonal_int_vectors_not_agree_on_regular :
    ∀ (q n : ℕ) (ω : ℂ) (a b : ℕ → ℤ), 2 ≤ q → 0 < n → IsPrimitiveRoot ω (q ^ n - 1) → ∑ k ∈ Finset.range (q ^ n - 1), a k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), b k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), a k * b k = 0 → 0 < (∑ k ∈ Finset.range (q ^ n - 1), a k) * (∑ k ∈ Finset.range (q ^ n - 1), b k) → (∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) → ∑ k ∈ Finset.range (q ^ n - 1), (a k : ℂ) * ω ^ (j * k) = ∑ k ∈ Finset.range (q ^ n - 1), (b k : ℂ) * ω ^ (j * k)) → False := by
  intro q n ω a b hq hn hω ha2 hb2 hab hpos hreg
  have hN : 0 < q ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (by omega))
  have hc2 : ∑ k ∈ Finset.range (q ^ n - 1), (a k - b k) ^ 2 = 2 * (n : ℤ) := by
    have e : ∀ k, (a k - b k) ^ 2 = a k ^ 2 + b k ^ 2 - 2 * (a k * b k) := fun k => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ha2, hb2, hab]
    ring
  have hcoef : ∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) →
      ∑ k ∈ Finset.range (q ^ n - 1), (((a k - b k : ℤ)) : ℂ) * ω ^ (j * k) = 0 := by
    intro j hj
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hreg j hj, sub_self]
  by_cases hexc : q = 2 ∧ (n = 4 ∨ n = 6)
  · obtain ⟨rfl, rfl | rfl⟩ := hexc
    · refine GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h5 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h5
            interval_cases j <;> interval_cases e <;> decide))
    · refine GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h21 h9 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h21 h9
            interval_cases j <;> interval_cases e <;> decide))
  · have hsum : |∑ k ∈ Finset.range (q ^ n - 1), (a k - b k)| ≤ (n : ℤ) - 1 := by
      rw [Finset.sum_sub_distrib]
      have hA := abs_le.mp ((abs_sum_le_sum_sq_int _ a).trans ha2.le)
      have hB := abs_le.mp ((abs_sum_le_sum_sq_int _ b).trans hb2.le)
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_le.mpr ⟨by omega, by omega⟩
    have h1 := GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport n (q ^ n - 1) ω (fun k => a k - b k)
      ((Finset.Ioo 0 (q ^ n - 1)).filter
        (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1]))
      hn hN hω hc2 hsum (fun j hj0 hjN hjS => by
        refine hcoef j (fun e he1 he2 he => hjS ?_)
        simp only [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨hj0, hjN⟩, e, ⟨he1, he2⟩, he⟩)
    have h2 := GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le q n hq hn
    have h3 := GlobalTheory.T.separation_numerical_ineq_cuspidalGL q n hq hn hexc
    exact absurd (lt_of_le_of_lt (h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _)) h3)
      (lt_irrefl _)

end GlobalTheory.CuspGL
end
end
