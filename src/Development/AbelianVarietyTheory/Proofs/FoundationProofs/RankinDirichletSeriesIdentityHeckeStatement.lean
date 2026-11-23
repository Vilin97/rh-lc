module

public import Mathlib.NumberTheory.LSeries.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableMulDivisorSumStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSquaresEqStatement
import Mathlib.Algebra.Order.Star.Real
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinConvolutionCoeffStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableBoundedMulOfSummableNormSq

section

@[expose] public section

open Complex Filter Topology

namespace GlobalTheory

theorem lSeriesSummable_bounded_mul_of_summable_normSq :
    ∀ (e : ℕ) (θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => θ n * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e θ g s he hs hθ hg
  have h1 := hg s hs
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ ((2 * (e : ℝ) + s) - 1) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded ((h1.add h2).div_const 2) ?_
  intro n
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have e1 : (((2 * e + 1 : ℕ) : ℝ) + s) = (2 * (e : ℝ) + s) + 1 := by push_cast; ring
    rw [Complex.ofReal_re, e1, Real.rpow_add_one hn'.ne', Real.rpow_sub_one hn'.ne']
    have hN : (0 : ℝ) < (n : ℝ) ^ (2 * (e : ℝ) + s) := Real.rpow_pos_of_pos hn' _
    generalize (n : ℝ) ^ (2 * (e : ℝ) + s) = N at hN ⊢
    have hb : ‖θ n * g n‖ ≤ ‖g n‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hθ n)
    calc ‖θ n * g n‖ / N ≤ ‖g n‖ / N := by gcongr
      _ ≤ (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 := by
        have : (‖g n‖ ^ 2 / (N * n) + 1 / (N / n)) / 2 - ‖g n‖ / N
            = (‖g n‖ - n) ^ 2 / (2 * N * n) := by field_simp; ring
        have h3 : 0 ≤ (‖g n‖ - n) ^ 2 / (2 * N * n) := by positivity
        linarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LSeriesSummableBoundedMulOfSummableNormSqStatement

section

@[expose] public section

open Complex Filter Topology

theorem _root_.GlobalTheory.T.lSeriesSummable_bounded_mul_of_summable_sq_div : ∀ (e : ℕ) (θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖θ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => θ n * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  first | exact @GlobalTheory.lSeriesSummable_bounded_mul_of_summable_normSq | exact GlobalTheory.lSeriesSummable_bounded_mul_of_summable_normSq | (intros; apply GlobalTheory.lSeriesSummable_bounded_mul_of_summable_normSq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesShiftTwist

section

@[expose] public section

open Complex Filter Topology

namespace GlobalTheory

theorem lseries_shift_twist (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ) (he : 1 ≤ e) :
    LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  unfold LSeries
  congr 1
  funext n
  simp only [LSeries.term_def]
  split_ifs with hn
  · rfl
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have key : (n : ℂ) ^ (((2 * (e : ℝ) + s : ℝ)) : ℂ) =
      (n : ℂ) ^ (e - 1) * (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hn']
    congr 1
    push_cast [Nat.cast_sub he]
    ring
  have h1 : (n : ℂ) ^ (e - 1) ≠ 0 := pow_ne_zero _ hn'
  have h2 : (n : ℂ) ^ ((((e + 1 : ℝ) + s : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [key]
  field_simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesShiftTwistStatement

section

@[expose] public section

open Complex Filter Topology

theorem _root_.GlobalTheory.T.lSeries_twist_natPow_eq_shift : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  first | exact @GlobalTheory.lseries_shift_twist | exact GlobalTheory.lseries_shift_twist | (intros; apply GlobalTheory.lseries_shift_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSummableTwistPowOfSqSummable

section

@[expose] public section

open Complex Filter Topology

namespace GlobalTheory

theorem lseriesSummable_twist_pow_of_sq_summable :
    ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  intro e ψ g s he hs hψ hg
  have h1 := hg s hs
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded (h1.add h2) fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hx : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    simp only [Complex.ofReal_re, norm_mul, norm_pow, Complex.norm_natCast, Nat.add_sub_cancel]
    set x : ℝ := (n : ℝ) with hxdef
    set A : ℝ := ‖g n‖ with hA
    have hA0 : 0 ≤ A := norm_nonneg _
    set p : ℝ := x ^ (-(2 * (k : ℝ) + 3 + s) / 2) with hp
    set q : ℝ := x ^ (-(1 + s) / 2) with hq
    have hp0 : 0 ≤ p := by positivity
    have hq0 : 0 ≤ q := by positivity
    have e1 : A ^ 2 / x ^ (((2 * (k + 1) + 1 : ℕ) : ℝ) + s) = (A * p) ^ 2 := by
      rw [mul_pow, hp, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, div_eq_mul_inv,
        ← Real.rpow_neg hx.le]
      congr 2
      push_cast
      ring
    have e2 : 1 / x ^ (1 + s) = q ^ 2 := by
      rw [hq, ← Real.rpow_natCast (x ^ _) 2, ← Real.rpow_mul hx.le, one_div,
        ← Real.rpow_neg hx.le]
      congr 1
      push_cast
      ring
    have e3 : x ^ k / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = p * q := by
      rw [hp, hq, ← Real.rpow_natCast x k, ← Real.rpow_sub hx, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    rw [e1, e2]
    have e4 : ‖ψ n‖ * x ^ k * A / x ^ (2 * ((k + 1 : ℕ) : ℝ) + s) = ‖ψ n‖ * (A * p * q) := by
      rw [mul_assoc A, ← e3]; ring
    rw [e4]
    have h3 : ‖ψ n‖ * (A * p * q) ≤ A * p * q :=
      mul_le_of_le_one_left (by positivity) (hψ n)
    have h4 : 0 ≤ A * p * q := by positivity
    nlinarith [sq_nonneg (A * p - q)]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesSummableTwistPowOfSqSummableStatement

section

@[expose] public section

open Complex Filter Topology

theorem _root_.GlobalTheory.T.lSeriesSummable_twist_pow_of_summable_sq_div : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ n, ‖ψ n‖ ≤ 1) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → LSeriesSummable (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) := by
  first | exact @GlobalTheory.lseriesSummable_twist_pow_of_sq_summable | exact GlobalTheory.lseriesSummable_twist_pow_of_sq_summable | (intros; apply GlobalTheory.lseriesSummable_twist_pow_of_sq_summable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinDirichletSeriesIdentityHecke

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem rankin_dirichlet_identity : ∀ (e : ℕ) (χ ψ θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → ∀ b : ℕ → ℂ, (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) ∧ LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) * LSeries (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => θ n * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  intro e χ ψ θ g s he hs hψ hθ hn hg hsum b hb
  have hGB := GlobalTheory.T.lSeriesSummable_mul_divisorSum' e ψ θ g b s he hs (fun n => ⟨(hn n).2.1, (hn n).2.2⟩) hsum hb
  have hU := GlobalTheory.T.lSeriesSummable_twist_pow_of_summable_sq_div e ψ g s he hs (fun n => (hn n).2.1) hsum
  have hV := GlobalTheory.T.lSeriesSummable_bounded_mul_of_summable_sq_div e θ g s he hs (fun n => (hn n).2.2) hsum
  have hz := GlobalTheory.T.lSeries_squares_eq_shift e χ ψ θ s he hs hn
  refine ⟨hGB, ?_⟩
  rw [← hz.2, ← LSeries_convolution' hz.1 hGB, ← GlobalTheory.T.lSeries_twist_natPow_eq_shift e ψ g s he, ← LSeries_convolution' hU hV]
  exact LSeries_congr (fun {n} hn0 => (GlobalTheory.T.convolution_twist_eq_convolution_squares e χ ψ θ g b hψ hθ hg hb n hn0).symm) _

end GlobalTheory.EisM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinDirichletSeriesIdentityHeckeStatement

section

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.rankin_dirichlet_series_identity_hecke : ∀ (e : ℕ) (χ ψ θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → ∀ b : ℕ → ℂ, (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) ∧ LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) * LSeries (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => θ n * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  first | exact @GlobalTheory.EisM.rankin_dirichlet_identity | exact GlobalTheory.EisM.rankin_dirichlet_identity | (intros; apply GlobalTheory.EisM.rankin_dirichlet_identity <;> assumption)
end
end
