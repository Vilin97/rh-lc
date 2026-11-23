module

public import Formalism.FormalGroupWitt.Statement
public import Formalism.FormalGroupWitt.SubstInjectiveV
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationSubstVector
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.InvIntV
public import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV

-- Source module: Formalism.FormalGroupWitt.FormalGroupWittProofs.CoeffExpandEqZero

section

@[expose] public section

noncomputable section

universe u v w

namespace Formalism.FG.LowCoefficients

open Formalism.G

theorem coeff_expand_eq_zero {R : Type*} [CommRing R] {τ : Type*} (q : ℕ) (hq : q ≠ 0)
    (hq2 : 2 ≤ q) (φ : MvPowerSeries τ R) (N : ℕ) (hN : 1 ≤ N)
    (hlow : ∀ m : τ →₀ ℕ, m.degree < N → MvPowerSeries.coeff m φ = 0)
    (d : τ →₀ ℕ) (hd : d.degree = N) : MvPowerSeries.coeff d (MvPowerSeries.expand q hq φ) = 0 := by

  classical
  by_cases hdiv : ∀ i, q ∣ d i
  · let m : τ →₀ ℕ := d.mapRange (fun k => k / q) (by simp)
    have hdm : d = q • m := by
      ext i
      simp [m, Nat.mul_div_cancel' (hdiv i)]
    have hdeg : d.degree = q * m.degree := by
      rw [hdm, map_nsmul, smul_eq_mul]
    rw [hdm, MvPowerSeries.coeff_expand_smul]
    apply hlow
    have h1 : q * m.degree = N := by rw [← hdeg, hd]
    have h2 : 0 < m.degree := by
      rcases Nat.eq_zero_or_pos m.degree with h | h
      · rw [h, mul_zero] at h1
        omega
      · exact h
    nlinarith
  · push_neg at hdiv
    obtain ⟨i, hi⟩ := hdiv
    exact MvPowerSeries.coeff_expand_of_not_dvd q hq φ hi

end Formalism.FG.LowCoefficients

namespace Formalism.FG

open Formalism.G

theorem low_coeff_vector : Formalism.FG.LowCoeffV.{u, v, w} := by

  intro K _ _ p q hq σ hq2 ι _ M τ D hD N hN hlow j d hd
  have h1 := hD j d
  have h2 : MvPowerSeries.coeff d
      (∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (D k))) = 0 := by

    rw [map_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [map_smul, smul_eq_mul,
      LowCoefficients.coeff_expand_eq_zero q hq hq2 _ N hN (fun m hm => by rw [MvPowerSeries.coeff_map, hlow k m hm, map_zero]) d hd,
      mul_zero]
  rw [map_sub, map_smul, smul_eq_mul, h2, mul_zero, sub_zero] at h1
  exact h1

end Formalism.FG
end
end
end

-- Source module: Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector

section

@[expose] public section

noncomputable section

universe u v w

namespace Formalism.FG.FunctionalEquationHom

open Formalism.G Formalism.LT

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem integralMv_sub {τ : Type w} {a b : MvPowerSeries τ K} (ha : IntegralMv a)
    (hb : IntegralMv b) : IntegralMv (a - b) := by
  unfold IntegralMv at ha hb ⊢
  intro d
  rw [map_sub, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha d) ?_)
  rw [norm_neg]
  exact hb d

theorem funEqV_sub {ι : Type v} [Fintype ι] {τ : Type w} {p q : ℕ} (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) {a b : ι → MvPowerSeries τ K} (ha : IsFunEqTypeV p q hq σ M a)
    (hb : IsFunEqTypeV p q hq σ M b) : IsFunEqTypeV p q hq σ M (a - b) := by
  intro j
  convert integralMv_sub (ha j) (hb j) using 1
  simp only [Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]
  abel

theorem two_le_q {p q : ℕ} {σ : K →+* K} (h : FunctionalEquationSetting K p q σ) : 2 ≤ q := by
  unfold FunctionalEquationSetting at h
  obtain ⟨hp, ⟨k, hk, rfl⟩, -, -⟩ := h
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk

theorem main (hSol : Formalism.FG.SolveExistsV.{u, v, w}) (hInv : Formalism.FG.InvIntegralV.{u, v, w})
    (hLow : Formalism.FG.LowCoeffV.{u, v, w}) (hKey : Formalism.FG.FunEqSubstV.{u, v, w}) :
    Formalism.FG.FunEqHomV.{u, v, w} := by
  intro K _ _ _ p q hq σ hS ι _ _ M hM f hf hfF τ _ g hg0 hgF
  obtain ⟨h, h0, hsub⟩ := hSol K ι τ f g hf hg0
  refine ⟨h, h0, ?_, hsub⟩
  have hC : IsFunEqTypeV p q hq σ M (fun j => MvPowerSeries.subst h (f j)) := by
    have e : (fun j => MvPowerSeries.subst h (f j)) = g := funext hsub
    rw [e]
    exact hgF
  exact hInv K ι τ (IsFunEqTypeV p q hq σ M) f hf
    (fun a b ha hb => funEqV_sub hq σ M ha hb)
    (fun P hP0 hPI => hKey K p q hq σ hS ι M hM f hf.1 hfF τ P hP0 hPI)
    (fun D hD N hN hlow => hLow K p q hq σ (two_le_q hS) ι M τ D hD N hN hlow)
    h h0 hC

end Formalism.FG.FunctionalEquationHom

namespace Formalism.FG

theorem FunEqHomV_of (hSol : Formalism.FG.SolveExistsV.{u, v, w}) (hInv : Formalism.FG.InvIntegralV.{u, v, w})
    (hLow : Formalism.FG.LowCoeffV.{u, v, w}) (hKey : Formalism.FG.FunEqSubstV.{u, v, w}) :
    Formalism.FG.FunEqHomV.{u, v, w} :=
  FunctionalEquationHom.main hSol hInv hLow hKey

theorem functional_equation_hom_vector : Formalism.FG.FunEqHomV.{u, v, w} :=
  FunEqHomV_of solve_exists_vector inverse_integral_vector low_coeff_vector functional_equation_subst_vector

end Formalism.FG
end
end
end

-- Source module: Formalism.FormalGroupWitt.WeightInvariance

section

@[expose] public section

namespace Formalism.FG

universe u v w

theorem funEqHomV : FunEqHomV.{u, v, w} := functional_equation_hom_vector

end Formalism.FG
end
end
