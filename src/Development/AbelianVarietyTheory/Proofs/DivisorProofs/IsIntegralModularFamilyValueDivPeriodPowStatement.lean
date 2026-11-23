module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosureStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariantStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosedStatement
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.Vieta
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariantStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_eq_discriminant_pow_mul_eval_jInvariant : ∀ (R : Subring ℂ) (N w : ℕ) (f : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), f ∣[(12 * w : ℤ)] γ = f) → QAll (· ∈ R) N f → ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ R) ∧ ∀ τ, f τ = DD τ ^ w * P.eval (jT τ) := by
  first | exact @GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT | exact GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT | (intros; apply GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmPowTwelveDivDiscriminantMemSubring

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem esymm_pow_twelve_div_mem : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f →
    (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ,
    (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by
  intro ι _ act w N f R τ₀ hN hact hf hq hj k
  have hF : IsFam act ((12 : ℕ) * (w : ℤ)) fun i τ => f i τ ^ 12 :=
    (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.2.2.1 w f 12 hf
  obtain ⟨-, -, -, -, hpow, hsp⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hqS : QAll (· ∈ R) N fun τ =>
      ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ ^ 12 :=
    (hsp (Finset ι) (Finset.powersetCard k Finset.univ) (fun t τ => ∏ i ∈ t, f i τ ^ 12)
      fun t _ => (hsp ι t (fun i τ => f i τ ^ 12) fun i _ => hpow (f i) 12 (hq i)).2).1
  have hw : ((k : ℤ) * (((12 : ℕ) : ℤ) * (w : ℤ))) = 12 * ((k * w : ℕ) : ℤ) := by
    push_cast; ring
  obtain ⟨P, hP, hPe⟩ := GlobalTheory.T.exists_eq_discriminant_pow_mul_eval_jInvariant R N (k * w) _ hN (fun γ => by
    have h := (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hF γ).2 k
    rw [hw] at h
    exact h) hqS
  have hD : DD τ₀ ^ (k * w) ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ₀)
  have hsum : (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) =
      (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12) / DD τ₀ ^ (k * w) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp ht).2, ← pow_mul,
      mul_comm w k]
  have h0 := hPe τ₀
  rw [hsum, h0, mul_div_cancel_left₀ _ hD, Polynomial.eval_eq_sum_range]
  exact R.sum_mem fun i _ => R.mul_mem (hP i) (R.pow_mem hj i)

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmPowTwelveDivDiscriminantMemSubringStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by
  first | exact @GlobalTheory.QFam.esymm_pow_twelve_div_mem | exact GlobalTheory.QFam.esymm_pow_twelve_div_mem | (intros; apply GlobalTheory.QFam.esymm_pow_twelve_div_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubring

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open Polynomial

namespace GlobalTheory.QFam

theorem isIntegral_of_esymm_mem (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ)
    (h : ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) (i : ι) :
    IsIntegral R (x i) := by
  classical
  set Q : ℂ[X] := ∏ j, (X + C (x j)) with hQ
  have hmon : Q.Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))
  have hdeg : Q.natDegree = (Finset.univ : Finset ι).card := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))]
    simp
  have hl : Q ∈ Polynomial.lifts (algebraMap R ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ (Finset.univ : Finset ι).card
    · rw [hQ, Finset.prod_X_add_C_coeff _ _ hn]
      exact ⟨⟨_, h _⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
  have hneg : IsIntegral R (-x i) := by
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  simpa using hneg.neg

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubringStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.isIntegral_of_esymm_mem_subring : ∀ (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ), (∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) → ∀ i, IsIntegral R (x i) := by
  first | exact @GlobalTheory.QFam.isIntegral_of_esymm_mem | exact GlobalTheory.QFam.isIntegral_of_esymm_mem | (intros; apply GlobalTheory.QFam.isIntegral_of_esymm_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPow

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)

namespace GlobalTheory.QFam

theorem isIntegral_value_div (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ) (hN : 0 < N) (hact : ActBij act)
    (hf : IsFam act w f) (hq : ∀ i, QAll (· ∈ R) N (f i)) (hj : IsIntegral R (jT τ₀))
    (hΩ : Ω ^ 12 = DD τ₀) (i : ι) : IsIntegral R (f i τ₀ / Ω ^ w) := by
  have hq' : ∀ i, QAll (· ∈ (integralClosure R ℂ).toSubring) N (f i) := fun i => by
    obtain ⟨a, ha, haR⟩ := hq i
    exact ⟨a, ha, fun n => (integralClosure R ℂ).algebraMap_mem ⟨a n, haR n⟩⟩
  have hs := GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring ι act w N f (integralClosure R ℂ).toSubring τ₀ hN hact hf hq' hj
  have h1 : IsIntegral (integralClosure R ℂ) (f i τ₀ ^ 12 / DD τ₀ ^ w) :=
    GlobalTheory.T.isIntegral_of_esymm_mem_subring ι (integralClosure R ℂ).toSubring (fun i => f i τ₀ ^ 12 / DD τ₀ ^ w) hs i
  have h2 : IsIntegral R (f i τ₀ ^ 12 / DD τ₀ ^ w) := isIntegral_trans _ h1
  have h3 : (f i τ₀ / Ω ^ w) ^ 12 = f i τ₀ ^ 12 / DD τ₀ ^ w := by
    rw [div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm]
  exact IsIntegral.of_pow (n := 12) (by norm_num) (h3 ▸ h2)

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPowStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → IsIntegral R (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsIntegral R (f i τ₀ / Ω ^ w) := by
  first | exact @GlobalTheory.QFam.isIntegral_value_div | exact GlobalTheory.QFam.isIntegral_value_div | (intros; apply GlobalTheory.QFam.isIntegral_value_div <;> assumption)
end
end
