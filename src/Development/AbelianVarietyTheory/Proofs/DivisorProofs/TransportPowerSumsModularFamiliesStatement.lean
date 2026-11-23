module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjEisensteinPolynomialLevelOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosureStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjEisensteinPolynomialLevelOneStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → ∃ (s : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ), (∀ p ∈ s, 4 * p.1 + 6 * p.2 = w) ∧ (∀ τ, F τ = ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ∧ ∀ τ, F' τ = ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := by
  first | exact @GlobalTheory.QFam.levelPoly_conj | exact GlobalTheory.QFam.levelPoly_conj | (intros; apply GlobalTheory.QFam.levelPoly_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneModularFormValueGaloisTransport

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isobaric_monomial_div (c x y ω : ℂ) (a b w : ℕ) (h : 4 * a + 6 * b = w) :
    c * (x ^ a * y ^ b) / ω ^ w = c * ((x / ω ^ 4) ^ a * (y / ω ^ 6) ^ b) := by
  rw [div_pow, div_pow, ← pow_mul, ← pow_mul, div_mul_div_comm, ← pow_add, h, mul_div_assoc]

theorem levelOne_value_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  intro g w N F F' τ₀ τ₁ ω₀ ω₁ hN hF hq h4 h6
  obtain ⟨s, c, hs, h0, h1⟩ := GlobalTheory.T.exists_conj_eisensteinPolynomial_levelOne g w N F F' hN hF hq

  rw [h0, h1, Finset.sum_div, Finset.sum_div, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp), isobaric_monomial_div _ _ _ _ _ _ _ (hs p hp),
    map_mul, map_mul, map_pow, map_pow, h4, h6]

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneModularFormValueGaloisTransportStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.levelOne_modularForm_value_galois_transport : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F F' : ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → QConj g N F F' → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → g (F τ₀ / ω₀ ^ w) = F' τ₁ / ω₁ ^ w := by
  first | exact @GlobalTheory.QFam.levelOne_value_transport | exact GlobalTheory.QFam.levelOne_value_transport | (intros; apply GlobalTheory.QFam.levelOne_value_transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerSumsModularFamilies

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem sum_prod_pow_div_pow {ι S : Type} [Fintype ι] [Fintype S] (m μ : S → ℕ) (x : S → ι → ℂ)
    (ω : ℂ) :
    (∑ i, ∏ s, x s i ^ μ s) / ω ^ (∑ s, μ s * m s) = ∑ i, ∏ s, (x s i / ω ^ m s) ^ μ s := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  simp only [mul_comm]

theorem transport_power_sums : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by
  intro g ι S _ _ act N m f f' τ₀ τ₁ ω₀ ω₁ hN hact hfam hq h4 h6 μ
  obtain ⟨-, -, -, -, hpow, -, hprod, -⟩ := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act
  obtain ⟨-, -, -, -, qpow, qfin⟩ := GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure g N hN
  have hM : IsFam act (((∑ s, μ s * m s : ℕ) : ℤ)) fun i τ => ∏ s, f s i τ ^ μ s := by
    have := hprod S Finset.univ (fun s => (μ s : ℤ) * (m s : ℤ)) (fun s i τ => f s i τ ^ μ s)
      (fun s _ => hpow (m s) (f s) (μ s) (hfam s))
    push_cast
    exact this
  have hQ : QConj g N (fun τ => ∑ i, ∏ s, f s i τ ^ μ s) fun τ => ∑ i, ∏ s, f' s i τ ^ μ s :=
    (qfin ι Finset.univ (fun i τ => ∏ s, f s i τ ^ μ s) (fun i τ => ∏ s, f' s i τ ^ μ s)
      fun i _ => (qfin S Finset.univ (fun s τ => f s i τ ^ μ s) (fun s τ => f' s i τ ^ μ s)
        fun s _ => qpow _ _ (μ s) (hq s i)).2).1
  have key := GlobalTheory.T.levelOne_modularForm_value_galois_transport g (∑ s, μ s * m s) N _ _ τ₀ τ₁ ω₀ ω₁ hN
    (fun γ => (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hM γ).1) hQ h4 h6
  rw [sum_prod_pow_div_pow m μ (fun s i => f s i τ₀), sum_prod_pow_div_pow m μ (fun s i => f' s i τ₁)] at key

  simpa only [map_sum, map_prod, map_pow] using key

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPowerSumsModularFamiliesStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.transport_power_sums_modular_families : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ μ : S → ℕ, ∑ i, ∏ s, g (f s i τ₀ / ω₀ ^ m s) ^ μ s = ∑ i, ∏ s, (f' s i τ₁ / ω₁ ^ m s) ^ μ s := by
  first | exact @GlobalTheory.QFam.transport_power_sums | exact GlobalTheory.QFam.transport_power_sums | (intros; apply GlobalTheory.QFam.transport_power_sums <;> assumption)
end
end
