module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevelStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinJetSplitLatticeStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k * (a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t))) (jet k (split 𝔞 𝔟 x) κ τ c t) := by
  first | exact @GlobalTheory.HilbFam.hasSum_jet_split | exact GlobalTheory.HilbFam.hasSum_jet_split | (intros; apply GlobalTheory.HilbFam.hasSum_jet_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagHomogeneous

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem lag_homogeneous : ∀ (k n : ℕ) (c y v : ℂ), lag k n (v * c) (v * y) = v ^ n * lag k n c y ∧ lag k n 0 y = y ^ n := by
  intro k n c y v
  refine ⟨?_, ?_⟩
  · unfold lag
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have h : v ^ n = v ^ (n - m) * v ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
    rw [h, mul_pow, mul_pow]; ring
  · unfold lag
    rw [Finset.sum_range_succ, Finset.sum_eq_zero]
    · simp [rco]
    · intro m hm
      have hmn : n - m ≠ 0 := Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hm)
      simp [hmn]

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitSmulDirection

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem jet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t v κ hk ha hτ
  have h1 := GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ (v * c) (v * t) κ hk ha hτ
  have h2 := (GlobalTheory.T.hasSum_hilbertEisenstein_jet_split_lattice F k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ).mul_left (v ^ (∑ i, κ i))
  refine h1.unique (HasSum.congr_fun h2 fun ξ ↦ ?_)
  have hp : (∏ i : Emb F, lag k (κ i) (v * c) ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t))) =
      v ^ (∑ i, κ i) * ∏ i : Emb F, lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [show (2 * Real.pi * Complex.I) * (i ξ : ℂ) * (v * t) = v * ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t) by ring]
    exact (lag_homogeneous k (κ i) c _ v).1
  rw [hp]; ring

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitSmulDirectionStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet k (split 𝔞 𝔟 x) κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_split_smul_direction | exact GlobalTheory.HilbFam.jet_split_smul_direction | (intros; apply GlobalTheory.HilbFam.jet_split_smul_direction <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirection

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

set_option autoImplicit false

namespace GlobalTheory.HilbFam

theorem jet_smul_dir_of_hasLevel : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet (2 * s) L κ τ c t := by
  intro hE F _ _ _ hf s N L hs hN hL τ c t v κ hτ
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, -, hc⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  exact GlobalTheory.T.hilbertEisensteinLatticeJet_split_smul_direction F (2 * s) 𝔞 𝔟 _ a x τ c t v κ (even_two_mul s) hc hτ

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetSmulDirectionStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_smul_direction : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (τ c t v : ℂ) (κ : Emb F → ℕ), 0 < τ.im → jet (2 * s) L κ τ (v * c) (v * t) = v ^ (∑ i, κ i) * jet (2 * s) L κ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel | exact GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel | (intros; apply GlobalTheory.HilbFam.jet_smul_dir_of_hasLevel <;> assumption)
end
end
