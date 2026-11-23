module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import Mathlib.RingTheory.RegularLocalRing.Defs
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeLeRankMulSlope
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CentralizerCmFieldInvolution

section

@[expose] public section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.DualFlag

theorem abel_sum_rev : ∀ (n : ℕ) (b : Fin (n + 1) → ℝ) (e : Fin (n + 2) → ℝ), e 0 = 0 →
    (∑ i : Fin (n + 1), b i * (e i.rev.succ - e i.rev.castSucc)) =
      (∑ i : Fin n, (b i.castSucc - b i.succ) * (-e i.rev.succ.castSucc)) +
        b 0 * e (Fin.last (n + 1)) := by
  intro n
  induction n with
  | zero =>
    intro b e h0
    simp [h0]
  | succ n ih =>
    intro b e h0
    have h := ih (fun i => b i.succ) (fun i => e i.castSucc) (by simpa using h0)
    have hL := Fin.sum_univ_succ (fun i : Fin (n + 2) => b i * (e i.rev.succ - e i.rev.castSucc))
    have hR := Fin.sum_univ_succ
      (fun i : Fin (n + 1) => (b i.castSucc - b i.succ) * (-e i.rev.succ.castSucc))
    simp only [Fin.rev_succ, Fin.rev_zero, Fin.succ_last, Fin.castSucc_zero,
      Fin.succ_zero_eq_one, Fin.succ_castSucc] at h hL hR
    rw [hL, hR]
    linear_combination h

end GlobalTheory.CompanionTheory.DualFlag
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibrePowerMapOfTotalSpacesIsPullback

section

@[expose] public section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.AbelFlag

theorem abel_summation_flag : ∀ (n : ℕ) (a : Fin (n + 1) → ℝ) (d : Fin (n + 2) → ℝ), d 0 = 0 →
    -(∑ i : Fin (n + 1), a i * (d i.succ - d i.castSucc)) =
      (∑ i : Fin n, (a i.castSucc - a i.succ) * (-d i.succ.castSucc))
        + a (Fin.last n) * (-d (Fin.last (n + 1))) := by
  intro n
  induction n with
  | zero =>
    intro a d h
    simp [h]
  | succ n ih =>
    intro a d h
    have key := ih (fun i => a i.castSucc) (fun i => d i.castSucc) (by simpa using h)
    rw [Fin.sum_univ_castSucc (n := n + 1), Fin.sum_univ_castSucc (n := n)
      (f := fun i : Fin (n + 1) => (a i.castSucc - a i.succ) * (-d i.succ.castSucc))]
    simp only [Fin.succ_castSucc, Fin.succ_last] at key ⊢
    linear_combination key

end GlobalTheory.CompanionTheory.AbelFlag
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.NormDegreeStepZero

section

@[expose] public section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Decomp

theorem normDegree_step_zero {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K} {r : ℕ}
    (A : SatFlag E r) : E.normDegree (A.F 0) = 0 := by
  have h : A.F 0 = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := A.F 0)).mp (A.rank 0)
  rw [HermitianBundle.normDegree, h, HermitianBundle.degree_bot, zero_div]

theorem lamDeg_eq : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ), A.lamDeg lam = ∑ τ, ((∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) * (-E.normDegree ((A.W τ).F i.succ.castSucc))) + (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) * (-E.normDegree (A.W τ).top) + (∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) * (-E.normDegree ((A.S τ).F i.rev.succ.castSucc))) - lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ) := by
  intro K _ _ E Ψ _ j k A lam
  unfold FlagPair.lamDeg
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hW := GlobalTheory.CompanionTheory.AbelFlag.abel_summation_flag j (fun i => lam τ (Fin.castAdd (k + 1) i))
    (fun i => E.normDegree ((A.W τ).F i)) (normDegree_step_zero (A.W τ))
  have hS := GlobalTheory.CompanionTheory.DualFlag.abel_sum_rev k (fun i => lam τ (Fin.natAdd (j + 1) i))
    (fun i => E.normDegree ((A.S τ).F i)) (normDegree_step_zero (A.S τ))
  simp only [SatFlag.grDeg, FlagPair.flatDeg, SatFlag.top]
  linear_combination hW + hS

end GlobalTheory.CompanionTheory.Ar.Decomp
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeLeRankMulSlopeStatement

section

@[expose] public section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.normalized_degree_le_rank_mul_slope : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (μ : ℝ), E.slopeMax ≤ (μ : EReal) → ∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E.rank F * μ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le | exact GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le | (intros; apply GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedFlagDegreeLowerBound

section

@[expose] public section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.LowerAny

theorem sum_sub_succ (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.castSucc - f i.succ) = f 0 - f (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc, Fin.castSucc_zero] at h ⊢
    rw [h, Fin.succ_last]
    simp

theorem sum_weight_lower {n : ℕ} (a d : Fin n → ℝ) (M : ℝ) (ha : ∀ i, 0 ≤ a i) (hd : ∀ i, d i ≤ M) :
    -((∑ i, a i) * M) ≤ ∑ i, a i * (-d i) := by
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [mul_le_mul_of_nonneg_left (hd i) (ha i)]

theorem step_le {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K} {r : ℕ} (A : SatFlag E r)
    (μ : ℝ) (N : ℝ) (hμ : 0 ≤ μ) (hE : E.slopeMax ≤ (μ : EReal)) (hN : (r : ℝ) ≤ N) (i : Fin (r + 1)) :
    E.normDegree (A.F i) ≤ N * μ := by
  have h := GlobalTheory.T.normalized_degree_le_rank_mul_slope K E μ hE (A.F i)
  rw [A.rank i] at h
  have hi : ((i : ℕ) : ℝ) ≤ N := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) hN
  exact h.trans (mul_le_mul_of_nonneg_right hi hμ)

theorem term_lower {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ]
    (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ)
    (τ : Ψ) (hanti : Antitone (lam τ)) (hΛ : ∀ i, |lam τ i| ≤ Λ) (hμ : 0 ≤ μ)
    (hE : E.slopeMax ≤ (μ : EReal)) (hC : |A.flatDeg τ| ≤ C) :
    -(2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C) ≤
      (∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) *
          (-E.normDegree ((A.W τ).F i.succ.castSucc))) +
        (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) *
          (-E.normDegree (A.W τ).top) +
        (∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) *
          (-E.normDegree ((A.S τ).F i.rev.succ.castSucc))) -
        lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set N : ℝ := (j : ℝ) + 1 + ((k : ℝ) + 1) with hNdef
  have hNW : (((j + 1 : ℕ)) : ℝ) ≤ N := by push_cast; linarith
  have hNS : (((k + 1 : ℕ)) : ℝ) ≤ N := by push_cast; linarith
  have hN0 : 0 ≤ N := by linarith
  have hM : 0 ≤ N * μ := mul_nonneg hN0 hμ
  have hg : ∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) =
      lam τ (Fin.castAdd (k + 1) 0) - lam τ (Fin.castAdd (k + 1) (Fin.last j)) :=
    sum_sub_succ j (fun i => lam τ (Fin.castAdd (k + 1) i))
  have hh : ∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) =
      lam τ (Fin.natAdd (j + 1) 0) - lam τ (Fin.natAdd (j + 1) (Fin.last k)) :=
    sum_sub_succ k (fun i => lam τ (Fin.natAdd (j + 1) i))
  have h1 := sum_weight_lower
    (fun i : Fin j => lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ))
    (fun i : Fin j => E.normDegree ((A.W τ).F i.succ.castSucc)) (N * μ)
    (fun i => sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp)))
    (fun i => step_le (A.W τ) μ N hμ hE hNW _)
  have h3 := sum_weight_lower
    (fun i : Fin k => lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ))
    (fun i : Fin k => E.normDegree ((A.S τ).F i.rev.succ.castSucc)) (N * μ)
    (fun i => sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp)))
    (fun i => step_le (A.S τ) μ N hμ hE hNS _)
  rw [hg] at h1
  rw [hh] at h3
  have hb : 0 ≤ lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0) :=
    sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp))
  have htop : E.normDegree (A.W τ).top ≤ N * μ := step_le (A.W τ) μ N hμ hE hNW (Fin.last _)
  have h2 : -((lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) * (N * μ)) ≤
      (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) *
        (-E.normDegree (A.W τ).top) := by
    nlinarith [mul_le_mul_of_nonneg_left htop hb]
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ (Fin.natAdd (j + 1) 0))
  have h4 : lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ ≤ Λ * C := by
    calc lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ
        ≤ |lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ| := le_abs_self _
      _ = |lam τ (Fin.natAdd (j + 1) 0)| * |A.flatDeg τ| := abs_mul _ _
      _ ≤ Λ * C := mul_le_mul (hΛ _) hC (abs_nonneg _) hΛ0
  have hfirst : lam τ (Fin.castAdd (k + 1) 0) ≤ Λ := (le_abs_self _).trans (hΛ _)
  have hlast : -Λ ≤ lam τ (Fin.natAdd (j + 1) (Fin.last k)) := (abs_le.mp (hΛ _)).1
  have h5 : (lam τ (Fin.castAdd (k + 1) 0) - lam τ (Fin.natAdd (j + 1) (Fin.last k))) * (N * μ) ≤
      (2 * Λ) * (N * μ) := mul_le_mul_of_nonneg_right (by linarith) hM
  have h6 : 2 * Λ * N * μ = (2 * Λ) * (N * μ) := by ring
  rw [h6]
  nlinarith [h1, h2, h3, h4, h5]

theorem lamDeg_lower : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ), (∀ τ, Antitone (lam τ)) → (∀ τ i, |lam τ i| ≤ Λ) → 0 ≤ μ → E.slopeMax ≤ (μ : EReal) → (∀ τ, |A.flatDeg τ| ≤ C) → -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C)) ≤ A.lamDeg lam := by
  intro K _ _ E Ψ _ j k A lam Λ μ C hanti hΛ hμ hE hC
  rw [GlobalTheory.CompanionTheory.Ar.Decomp.lamDeg_eq]
  calc -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C))
      = ∑ _τ : Ψ, -(2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_neg]
    _ ≤ _ := Finset.sum_le_sum fun τ _ =>
        term_lower E Ψ j k A lam Λ μ C τ (hanti τ) (hΛ τ) hμ hE (hC τ)

end GlobalTheory.CompanionTheory.Ar.LowerAny
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedFlagDegreeLowerBoundStatement

section

@[expose] public section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.weighted_flag_degree_lower_bound : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ), (∀ τ, Antitone (lam τ)) → (∀ τ i, |lam τ i| ≤ Λ) → 0 ≤ μ → E.slopeMax ≤ (μ : EReal) → (∀ τ, |A.flatDeg τ| ≤ C) → -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C)) ≤ A.lamDeg lam := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower | exact GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower | (intros; apply GlobalTheory.CompanionTheory.Ar.LowerAny.lamDeg_lower <;> assumption)
end
end
