module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinJetSplitLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreSignedBinomCoeffMul

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem rco_mul_rco : ∀ k n m j : ℕ, j ≤ m → m ≤ n →
    rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  intro k n m j hjm hmn
  have h1 : n.choose m * m.choose j = n.choose j * (n - j).choose (m - j) := by
    first
      | exact Nat.choose_mul hjm
      | exact Nat.choose_mul hmn hjm
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hjm
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have e1 : j + p + q - (j + p) = q := by omega
  have e2 : j + p - j = p := by omega
  have e3 : j + p + q - j = p + q := by omega
  have h2 : ∀ a p q : ℕ, a.ascFactorial p * (a + p).ascFactorial q = a.ascFactorial (p + q) := by
    intro a p q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [← add_assoc, Nat.ascFactorial_succ, Nat.ascFactorial_succ, ← ih, add_assoc a p q]
      ring
  have h3 := h2 (k + j) p q
  rw [e2, e3] at h1
  have h1' : ((j + p + q).choose (j + p) : ℤ) * ((j + p).choose j : ℤ)
      = ((j + p + q).choose j : ℤ) * ((p + q).choose p : ℤ) := by exact_mod_cast h1
  have h3' : ((k + j).ascFactorial p : ℤ) * ((k + (j + p)).ascFactorial q : ℤ)
      = ((k + j).ascFactorial (p + q) : ℤ) := by
    rw [← add_assoc]; exact_mod_cast h3
  unfold rco
  rw [e1, e2, e3, pow_add, ← h3']
  linear_combination ((-1 : ℤ) ^ p * (-1) ^ q * ((k + j).ascFactorial p : ℤ)
    * ((k + (j + p)).ascFactorial q : ℤ)) * h1'

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreSignedBinomCoeffMulStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.laguerreSignedBinomCoeff_mul : ∀ k n m j : ℕ, j ≤ m → m ≤ n → rco k n m * rco k m j = rco k n j * ((n - j).choose (m - j) : ℤ) := by
  first | exact @GlobalTheory.HilbFam.rco_mul_rco | exact GlobalTheory.HilbFam.rco_mul_rco | (intros; apply GlobalTheory.HilbFam.rco_mul_rco <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaguerreDerivativePolynomialValueAdd

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_add : ∀ (k n : ℕ) (c s y : ℂ), lag k n (c + s) y =
    ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y := by
  intro k n c s y
  have hR : ∑ m ∈ Finset.range (n + 1), (rco k n m : ℂ) * s ^ (n - m) * lag k m c y
      = ∑ j ∈ Finset.range (n + 1), ∑ m ∈ Finset.Ico j (n + 1),
        (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j) := by
    simp only [lag, Finset.mul_sum, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_Ico_comm 0 (n + 1) (fun j m ↦
      (rco k n m : ℂ) * s ^ (n - m) * ((rco k m j : ℂ) * c ^ (m - j) * y ^ j))).symm
  rw [hR, lag]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finset.sum_Ico_eq_sum_range, add_pow, show n + 1 - j = n - j + 1 by omega,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hp' : p ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  have h := GlobalTheory.T.laguerreSignedBinomCoeff_mul k n (j + p) j (by omega) (by omega)
  have e1 : j + p - j = p := by omega
  have e2 : n - (j + p) = n - j - p := by omega
  rw [e1] at h
  have h' : (rco k n (j + p) : ℂ) * (rco k (j + p) j : ℂ)
      = (rco k n j : ℂ) * ((n - j).choose p : ℂ) := by exact_mod_cast h
  rw [e1, e2]
  linear_combination (-(s ^ (n - j - p) * c ^ p * y ^ j)) * h'

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitDirectionAdd

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma piFinset_range_succ_eq_Iic {ι : Type} [Fintype ι] [DecidableEq ι] (κ : ι → ℕ) :
    Fintype.piFinset (fun i => Finset.range (κ i + 1)) = Finset.Iic κ := by
  ext μ
  simp [Fintype.mem_piFinset, Finset.mem_range, Finset.mem_Iic, Pi.le_def, Nat.lt_succ_iff]


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.jet_split_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ), Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * _root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) μ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have hμ := fun μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ =>
    ((_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ c t μ hk ha hτ).mul_left
      (((∏ i, _root_.GlobalTheory.HilbFam.rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i))))
  have hs := hasSum_sum (s := Finset.Iic κ) fun μ _ => hμ μ
  refine (_root_.GlobalTheory.HilbFam.hasSum_jet_split F k 𝔞 𝔟 a₀ a x τ (c + v) t κ hk ha hτ).unique
    (hs.congr_fun fun ξ => ?_)
  simp_rw [_root_.GlobalTheory.HilbFam.lag_add, Finset.prod_univ_sum, piFinset_range_succ_eq_Iic,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  ring

end GlobalTheory.HilbFam
end
end
