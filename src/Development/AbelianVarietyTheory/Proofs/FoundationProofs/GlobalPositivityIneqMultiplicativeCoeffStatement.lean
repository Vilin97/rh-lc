module

public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.PrimeCounting
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPositivityEulerFactorPrime
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
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLeStatement
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPositivityEulerFactorPrimeStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.local_positivity_eulerFactor_prime : ∀ (b ω : ℕ → ℂ) (s C : ℝ) (p : ℕ), 0 < s → p.Prime → b 1 = 1 → ‖ω p‖ = 1 → (∀ r : ℕ, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → Real.exp (‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ * ‖∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)‖ ^ 2 * (∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s)) * (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ := by
  first | exact @GlobalTheory.LocIneq.local_positivity_eulerFactor | exact GlobalTheory.LocIneq.local_positivity_eulerFactor | (intros; apply GlobalTheory.LocIneq.local_positivity_eulerFactor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowZetaTwoAddLeTwo

section

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem prod_Ico_inv_one_sub_inv_sq (M : ℕ) :
    ∏ n ∈ Finset.Ico 2 (M + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ = 2 * ((M : ℝ) + 1) / ((M : ℝ) + 2) := by
  induction M with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.prod_Ico_succ_top (by omega), ih]
    push_cast
    have h1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have h3 : (1 - 1 / ((k:ℝ) + 2) ^ 2) = ((k:ℝ)+1)*((k:ℝ)+3) / ((k:ℝ)+2)^2 := by
      field_simp; ring
    rw [h3]
    field_simp
    ring

theorem one_le_inv_one_sub_inv_sq {n : ℕ} (hn : 2 ≤ n) : 1 ≤ (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 1 / (n:ℝ)^2 := by positivity
  have hlt : 1 / (n:ℝ)^2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  exact one_le_inv₀ (by linarith) |>.mpr (by linarith)

theorem factor_le (s : ℝ) (hs : 0 ≤ s) {p : ℕ} (hp : 2 ≤ p) :
    (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (1:ℝ) ≤ p := by linarith
  have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  rw [Real.rpow_two] at hle
  have hsq : (4:ℝ) ≤ (p:ℝ)^2 := by nlinarith
  have hlt : 1 / (p:ℝ)^2 < 1 := by rw [div_lt_one (by positivity)]; linarith
  apply inv_anti₀
  · linarith
  · have : 1 / (p:ℝ) ^ (2 * (1 + s)) ≤ 1 / (p:ℝ)^2 :=
      one_div_le_one_div_of_le (by positivity) hle
    linarith

theorem prod_primesBelow_zeta_two_add_le_two :
    ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  intro s hs N
  have hsub : N.primesBelow ⊆ Finset.Ico 2 (N + 2) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨hp.2.two_le, by omega⟩
  have hmem : ∀ p ∈ N.primesBelow, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primesBelow hp).two_le
  calc ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹
      ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have := one_le_inv_one_sub_inv_sq (hmem p hp)
          have h2 := factor_le s hs (hmem p hp)

          have hp' : (2:ℝ) ≤ p := by exact_mod_cast hmem p hp
          have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          have hpos : 0 < (p:ℝ) ^ (2 * (1 + s)) := by positivity
          have hlt : 1 / (p:ℝ) ^ (2 * (1 + s)) < 1 := by
            rw [div_lt_one hpos]; rw [Real.rpow_two] at hle; nlinarith
          exact inv_nonneg.mpr (by linarith)
        · intro p hp; exact factor_le s hs (hmem p hp)
    _ ≤ ∏ n ∈ Finset.Ico 2 (N + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.prod_sdiff hsub]
        have h0 : 0 ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ :=
          Finset.prod_nonneg fun p hp => le_trans zero_le_one (one_le_inv_one_sub_inv_sq (hmem p hp))
        have h1 : 1 ≤ ∏ n ∈ Finset.Ico 2 (N + 2) \ N.primesBelow, (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
          apply Finset.one_le_prod₀
          intro n hn
          exact one_le_inv_one_sub_inv_sq (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hn).1).1
        nlinarith
    _ = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := prod_Ico_inv_one_sub_inv_sq N
    _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowZetaTwoAddLeTwoStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le : ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  first | exact @GlobalTheory.prod_primesBelow_zeta_two_add_le_two | exact GlobalTheory.prod_primesBelow_zeta_two_add_le_two | (intros; apply GlobalTheory.prod_primesBelow_zeta_two_add_le_two <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeff

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem tendsto_eulerProduct_LSeries_of_sq : ∀ (b : ℕ → ℂ) (s : ℝ), 0 < s → b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)) atTop (𝓝 (LSeries b ((1 + s : ℝ) : ℂ))) := by
  intro b s hs hb1 hmul hsum
  have hn : Summable (fun n : ℕ => ‖LSeries.term b ((1 + s : ℝ) : ℂ) n‖) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) :=
      Real.summable_one_div_nat_rpow.2 (by linarith)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hsum.add h1)
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · positivity
    · rw [Complex.ofReal_re, ← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (‖b n‖ - 1), norm_nonneg (b n)]
  refine EulerProduct.eulerProduct (f := LSeries.term b ((1 + s : ℝ) : ℂ)) ?_ ?_ hn ?_
  · simp [LSeries.term, hb1]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn0,
      LSeries.term_of_ne_zero (mul_ne_zero hm hn0), hmul m n hmn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, div_mul_div_comm]
  · simp

theorem prod_primesBelow_sq_le_tsum : ∀ (b : ℕ → ℂ) (s : ℝ), b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) ≤ ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro b s hb1 hmul hsum N
  have h0 : ∀ n : ℕ, 0 ≤ ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := fun n => by positivity
  have key := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) (by simp [hb1])
    (fun {m n} hmn => by
      simp only [hmul m n hmn, norm_mul, mul_pow, Nat.cast_mul]
      rw [Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm])
    (by simpa only [Real.norm_of_nonneg (h0 _)] using hsum) N
  rw [key]
  exact hsum.tsum_subtype_le _ _ h0

theorem global_positivity_ineq : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro M b ω s C hs hb1 hb0 hmul hbM hrec hC hsum X
  set f : ℕ → ℝ := fun n => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hf
  set Ssum := ∑' n : ℕ, f n
  set Lp : ℕ → ℂ := fun p => ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) with hLp
  set Rp : ℕ → ℝ := fun p => ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) with hRp
  set α : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ with hα
  set β : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ with hβ
  set A : ℕ → ℝ := fun p => if ¬ p ∣ M then ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) else 0 with hA
  have hA0 : ∀ p, 0 ≤ A p := fun p => by
    simp only [hA]; split_ifs <;> positivity

  have hα1 : ∀ p : ℕ, p.Prime → 1 ≤ α p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
    have h3 : 1 / (p : ℝ) ^ (1 + s) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hα]
    rw [one_le_inv₀ (by linarith)]; linarith
  have hβ1 : ∀ p : ℕ, p.Prime → 1 ≤ β p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (2 * (1 + s)) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (2 * (1 + s)) := by positivity
    have h3 : 1 / (p : ℝ) ^ (2 * (1 + s)) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hβ]
    rw [one_le_inv₀ (by linarith)]; linarith

  have hdiv : ∀ p : ℕ, p.Prime → p ∣ M → Lp p = 1 ∧ Rp p = 1 := by
    intro p hp hpM
    have hz : ∀ e : ℕ, e ≠ 0 → b (p ^ e) = 0 := by
      intro e he
      apply hbM
      intro hc
      have : p ∣ Nat.gcd (p ^ e) M := Nat.dvd_gcd (dvd_pow_self p he) hpM
      rw [hc] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    constructor
    · simp only [hLp]
      rw [tsum_eq_single 0]
      · simp [LSeries.term, hb1]
      · intro e he; simp [LSeries.term, hz e he]
    · simp only [hRp]
      rw [tsum_eq_single 0]
      · simp [hb1]
      · intro e he; simp [hz e he]
  have hRp0 : ∀ p, 0 ≤ Rp p := fun p => tsum_nonneg (fun e => by positivity)
  have hα0 : ∀ p : ℕ, p.Prime → 0 ≤ α p := fun p hp => le_trans zero_le_one (hα1 p hp)
  have hβ0 : ∀ p : ℕ, p.Prime → 0 ≤ β p := fun p hp => le_trans zero_le_one (hβ1 p hp)

  have hloc : ∀ p : ℕ, p.Prime → Real.exp (A p) ≤ α p * ‖Lp p‖ ^ 2 * Rp p * β p := by
    intro p hp
    by_cases hpM : p ∣ M
    · obtain ⟨h1, h2⟩ := hdiv p hp hpM
      simp only [hA, hpM, not_true_eq_false, if_false, Real.exp_zero, h1, h2, norm_one, one_pow, mul_one]
      nlinarith [hα1 p hp, hβ1 p hp]
    · have := GlobalTheory.T.local_positivity_eulerFactor_prime b ω s C p hs hp hb1 (hrec p 1 hp hpM).1 (fun r => (hrec p r hp hpM).2) hC
      simpa only [hA, hpM, not_false_eq_true, if_true] using this

  have hfin : ∀ N : ℕ, X ≤ N → Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by
    intro N hN
    have e1 : ∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) = ∑ p ∈ X.primesBelow, A p := by
      rw [Nat.primesBelow, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h1 : p.Prime <;> by_cases h2 : p ∣ M <;> simp [hA, h1, h2]
    have e2 : ∑ p ∈ X.primesBelow, A p ≤ ∑ p ∈ N.primesBelow, A p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesBelow_mono hN) (fun p _ _ => hA0 p)
    rw [e1]
    calc Real.exp (∑ p ∈ X.primesBelow, A p) ≤ Real.exp (∑ p ∈ N.primesBelow, A p) := Real.exp_le_exp.mpr e2
      _ = ∏ p ∈ N.primesBelow, Real.exp (A p) := Real.exp_sum _ _
      _ ≤ ∏ p ∈ N.primesBelow, (α p * ‖Lp p‖ ^ 2 * Rp p * β p) :=
          Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) (fun p hp => hloc p (Nat.prime_of_mem_primesBelow hp))
      _ = (∏ p ∈ N.primesBelow, α p) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * (∏ p ∈ N.primesBelow, Rp p) * (∏ p ∈ N.primesBelow, β p) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, norm_prod, Finset.prod_pow]
      _ ≤ (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum * 2 := by
          have a1 := GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le s hs N
          have a2 := GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le s hs.le N
          have a3 := prod_primesBelow_sq_le_tsum b s hb1 hmul hsum N
          have p1 : 0 ≤ ∏ p ∈ N.primesBelow, α p := Finset.prod_nonneg (fun p hp => hα0 p (Nat.prime_of_mem_primesBelow hp))
          have p2 : 0 ≤ ∏ p ∈ N.primesBelow, Rp p := Finset.prod_nonneg (fun p _ => hRp0 p)
          have p3 : 0 ≤ ∏ p ∈ N.primesBelow, β p := Finset.prod_nonneg (fun p hp => hβ0 p (Nat.prime_of_mem_primesBelow hp))
          gcongr
      _ = 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by ring
  have hlim := tendsto_eulerProduct_LSeries_of_sq b s hs hb1 hmul hsum
  have hcont : Tendsto (fun N : ℕ => 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum) atTop (𝓝 (2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * Ssum)) :=
    ((hlim.norm.pow 2).const_mul _).mul_const _
  exact ge_of_tendsto hcont (Filter.eventually_atTop.mpr ⟨X, hfin⟩)

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeffStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.global_positivity_ineq_multiplicative_coeff : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  first | exact @GlobalTheory.EisM.global_positivity_ineq | exact GlobalTheory.EisM.global_positivity_ineq | (intros; apply GlobalTheory.EisM.global_positivity_ineq <;> assumption)
end
end
