module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpInert

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_inert : ∀ (p N j : ℕ), 2 ≤ p → j ≤ N → HasSum (fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ |((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)| ≤ N / ((p : ℝ) - 1) := by
  intro p N j hp hjN
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hjN' : (j : ℝ) ≤ N := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpsq : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp0' : (p : ℝ) ≠ 0 := hp0.ne'
  have hp1' : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hpsq' : (p : ℝ) ^ 2 - 1 ≠ 0 := hpsq.ne'
  refine ⟨?_, ?_⟩
  · have hr1 : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have hg := hasSum_geometric_of_lt_one (by positivity) hr1
    have hE : HasSum (fun k : ℕ => (if Even (2 * k + 1) then (j : ℝ) else (N : ℝ) - j) /
        (p : ℝ) ^ (2 * k + 1)) (((N : ℝ) - j) / p * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
      have hf : (fun k : ℕ => (if Even (2 * k + 1) then (j : ℝ) else (N : ℝ) - j) /
          (p : ℝ) ^ (2 * k + 1)) = fun k => ((N : ℝ) - j) / p * ((p : ℝ) ^ 2)⁻¹ ^ k := by
        funext k
        rw [if_neg (Nat.not_even_two_mul_add_one k), inv_pow, ← pow_mul, pow_succ,
          ← div_eq_mul_inv, div_div, mul_comm ((p : ℝ) ^ (2 * k)) (p : ℝ)]
      rw [hf]
      exact hg.mul_left _
    have hO : HasSum (fun k : ℕ => (if Even (2 * k + 1 + 1) then (j : ℝ) else (N : ℝ) - j) /
        (p : ℝ) ^ (2 * k + 1 + 1)) ((j : ℝ) / (p : ℝ) ^ 2 * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹) := by
      have hf : (fun k : ℕ => (if Even (2 * k + 1 + 1) then (j : ℝ) else (N : ℝ) - j) /
          (p : ℝ) ^ (2 * k + 1 + 1)) = fun k => (j : ℝ) / (p : ℝ) ^ 2 * ((p : ℝ) ^ 2)⁻¹ ^ k := by
        funext k
        rw [if_pos ⟨k + 1, by ring⟩, inv_pow, ← pow_mul, ← div_eq_mul_inv, div_div, ← pow_add,
          show 2 * k + 1 + 1 = 2 + 2 * k by ring]
      rw [hf]
      exact hg.mul_left _
    have h := HasSum.even_add_odd (f := fun n : ℕ =>
      (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1)) hE hO
    have hinv : (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ = (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) := by
      rw [show (1 : ℝ) - ((p : ℝ) ^ 2)⁻¹ = ((p : ℝ) ^ 2 - 1) / (p : ℝ) ^ 2 by
        rw [sub_div, div_self (pow_ne_zero 2 hp0'), one_div], inv_div]
    have hv : (j : ℝ) / ((p : ℝ) - 1) + ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1) =
        ((N : ℝ) - j) / p * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ + (j : ℝ) / (p : ℝ) ^ 2 * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
      rw [hinv]
      field_simp
      ring
    rw [hv]
    exact h
  · have hA : |(N : ℝ) - 2 * j| ≤ N := abs_le.2 ⟨by linarith, by linarith⟩
    rw [abs_div, abs_mul, abs_of_pos hp0, abs_of_pos hpsq, div_le_div_iff₀ hpsq hp1]
    nlinarith [abs_nonneg ((N : ℝ) - 2 * j),
      mul_le_mul_of_nonneg_right hA (by nlinarith : (0 : ℝ) ≤ p * (p - 1)),
      mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hp1.le]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.EpSplit

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem ep_split : ∀ (p j : ℕ), 2 ≤ p →
    HasSum (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) ((j : ℝ) / ((p : ℝ) - 1)) := by
  intro p j hp
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by positivity
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hr : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs := (hasSum_geometric_of_lt_one (by positivity) hr).mul_left ((j : ℝ) / p)
  have hf : (fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1)) =
      fun n : ℕ => (j : ℝ) / p * (1 / (p : ℝ)) ^ n := by
    funext n
    rw [one_div_pow, pow_succ]
    field_simp
  have hv : (j : ℝ) / ((p : ℝ) - 1) = (j : ℝ) / p * (1 - 1 / (p : ℝ))⁻¹ := by
    rw [one_sub_div h0, inv_div]
    field_simp
  rw [hf, hv]
  exact hs

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.RootSurvey.GeometrySurvey.ExistsTopDegreeCoefficientFormAndEqOnTopForms

section

@[expose] public section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Flat.Bound₂

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_C_mul (a : ℝ) (Q : RP Ψ N) : degFl (C a * Q) = a * degFl Q := by
  unfold degFl
  simp only [coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

def rk (N j : ℕ) : Ψ ⊕ Ψ → ℝ
  | Sum.inl _ => j
  | Sum.inr _ => (N : ℝ) - j

def ep (N j p : ℕ) (fr : ℕ → Ψ ⊕ Ψ) : ℝ := (∑' n : ℕ, ((p : ℝ)⁻¹) ^ (n + 1) * rk N j (fr n)) - j / ((p : ℝ) - 1)

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem pLie_zero {j : ℕ} (hj : j ≤ N) (s : Ψ ⊕ Ψ) : (pLie j 0 s : RP Ψ N) = C (rk N j s) := by
  have hc : (Finset.univ.filter fun i : Fin N => (i : ℕ) < j).card = j := by
    rw [Fin.card_filter_val_lt]; omega
  have hc' : (Finset.univ.filter fun i : Fin N => j ≤ (i : ℕ)).card = N - j := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at this
    omega
  cases s with
  | inl τ => simp [pLie, pkLow, rk, hc]
  | inr τ => simp [pLie, rk, hc', Nat.cast_sub hj]

theorem delta_one {j : ℕ} (hj : j ≤ N) (p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ) (Q : RP Ψ N) :
    deltaTerm j p τ fr 1 Q = ep N j p fr * Real.log p * degFl Q := by
  have h2 : (pkLow j τ 0 : RP Ψ N) = C (j : ℝ) := pLie_zero hj (Sum.inl τ)
  unfold deltaTerm ep
  simp only [Nat.sub_self, pLie_zero hj, h2, degFl_C_mul, pow_one, ← mul_assoc]
  rw [tsum_mul_right]
  push_cast
  ring

variable (T : RootTower Ψ N) (II : IntersectionSystem)


omit [Fintype Ψ] [DecidableEq Ψ] in
theorem abs_ep_le {j p : ℕ} (hj : j ≤ N) (hp : 2 ≤ p) (fr : ℕ → Ψ ⊕ Ψ) : |ep N j p fr| ≤ N / ((p : ℝ) - 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hr0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hr1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hg : HasSum (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * N) (N / ((p : ℝ) - 1)) := by
    have := ((hasSum_geometric_of_lt_one hr0 hr1).mul_right (p : ℝ)⁻¹).mul_right (N : ℝ)
    have e : (1 - (p : ℝ)⁻¹)⁻¹ * (p : ℝ)⁻¹ * N = N / ((p : ℝ) - 1) := by
      have : (p : ℝ) ≠ 0 := by linarith
      have := h1.ne'
      field_simp
    rw [e] at this
    simpa only [pow_succ] using this
  have hrk : ∀ s : Ψ ⊕ Ψ, 0 ≤ rk N j s ∧ rk N j s ≤ N := by
    rintro (s | s) <;> simp only [rk] <;> constructor <;> linarith
  have hle : ∀ n : ℕ, ((p : ℝ)⁻¹) ^ (n + 1) * rk N j (fr n) ≤ ((p : ℝ)⁻¹) ^ (n + 1) * N := fun n =>
    mul_le_mul_of_nonneg_left (hrk _).2 (by positivity)
  have hnn : ∀ n : ℕ, 0 ≤ ((p : ℝ)⁻¹) ^ (n + 1) * rk N j (fr n) := fun n => mul_nonneg (by positivity) (hrk _).1
  have hs := Summable.of_nonneg_of_le hnn hle hg.summable
  have hU := hs.tsum_le_tsum hle hg.summable
  rw [hg.tsum_eq] at hU
  have hL : 0 ≤ ∑' n : ℕ, ((p : ℝ)⁻¹) ^ (n + 1) * rk N j (fr n) := tsum_nonneg hnn
  have a1 : (j : ℝ) / ((p : ℝ) - 1) ≤ N / ((p : ℝ) - 1) := by gcongr
  have a2 : 0 ≤ (j : ℝ) / ((p : ℝ) - 1) := by positivity
  unfold ep
  exact abs_le.2 ⟨by linarith, by linarith⟩

end GlobalTheory.CompanionTheory.Ar.Flat.Bound₂
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaTermLogDegreeBound

section

@[expose] public section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem deltaTerm_one : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  intro Ψ _ _ N j p τ fr hj hp
  refine ⟨Bound₂.ep N j p fr, Bound₂.abs_ep_le hj hp fr, fun h => ?_, fun h => ?_,
    fun Q => Bound₂.delta_one hj p τ fr Q⟩
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (j : ℝ) / (p : ℝ) ^ (n + 1) := by
      funext n
      obtain ⟨σ, hσ⟩ := h n
      rw [hσ, inv_pow, div_eq_inv_mul]
      rfl
    unfold Bound₂.ep
    rw [e, (ep_split p j hp).tsum_eq, sub_self]
  · have e : (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1) * Bound₂.rk N j (fr n)) =
        fun n : ℕ => (if Even (n + 1) then (j : ℝ) else (N : ℝ) - j) / (p : ℝ) ^ (n + 1) := by
      funext n
      rw [inv_pow, div_eq_inv_mul]
      congr 1
      rcases hs : fr n with σ | σ
      · have : Odd n := (h n).1 ⟨σ, hs⟩
        rw [if_pos this.add_one]
        rfl
      · have : ¬ Odd n := fun ho => by
          obtain ⟨σ', h'⟩ := (h n).2 ho
          rw [hs] at h'
          cases h'
        rw [if_neg (by simpa [Nat.even_add_one] using this)]
        rfl
    unfold Bound₂.ep
    rw [e, (ep_inert p N j hp hj).1.tsum_eq]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.DeltaTermLogDegreeBoundStatement

section

@[expose] public section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.delta_term_log_degree_bound : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ), j ≤ N → 2 ≤ p → ∃ e : ℝ, |e| ≤ N / ((p : ℝ) - 1) ∧ ((∀ n, ∃ σ, fr n = Sum.inl σ) → e = 0) ∧ ((∀ n, (∃ σ, fr n = Sum.inl σ) ↔ Odd n) → e = ((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) ∧ ∀ Q : RP Ψ N, deltaTerm j p τ fr 1 Q = e * Real.log p * degFl Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one | exact GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.deltaTerm_one <;> assumption)
end
end
