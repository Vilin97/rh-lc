module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AreaTauPair

section

@[expose] public section

noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.LatConst

theorem area_tauPair (τ : ℍ) : area (tauPair τ) = τ.im := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [area, h1, h2]
  simp [abs_of_pos τ.im_pos]

theorem wEta_one (τ : ℍ) : wEta (tauPair τ) 1 = EisensteinSeries.G2 τ := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  have h := (etaEisenstein (tauPair τ)).2
  rw [h1, h2] at h
  rw [h, one_mul, ← LegendreModelEllipticTorsion.tsum_e2Summand]
  refine tsum_congr fun m => ?_
  rw [EisensteinSeries.e2Summand]
  refine tsum_congr fun n => ?_
  simp [EisensteinSeries.eisSummand, zpow_ofNat]

theorem main : ∀ τ : ℍ, s2 (tauPair τ) = G2s τ ∧ area (tauPair τ) = τ.im := by
  intro τ
  refine ⟨?_, area_tauPair τ⟩
  have h := etaSplit (tauPair τ) 1
  rw [wEta_one, area_tauPair] at h
  rw [G2s, h]
  simp

end GlobalTheory.WpFam.LatConst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.TauVal

theorem complex_div_pow_div_div_pow (a x k : ℂ) (n : ℕ) (hk : k ≠ 0) :
    a / k ^ n / (x / k) ^ n = a / x ^ n := by
  by_cases hx : x = 0
  · subst hx
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · simp [zero_pow h.ne']
  · rw [div_pow]; field_simp

theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, Complex.I_ne_zero]

theorem main : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  intro Λ c Ω τ h
  obtain ⟨_, hP, hD, hs, _⟩ := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ h
  have hG := (GlobalTheory.WpFam.LatConst.main τ).1
  have hk := two_pi_I_ne_zero
  refine ⟨?_, fun N x => ⟨?_, ?_⟩⟩
  · rw [complex_div_pow_div_div_pow _ _ _ _ hk, hs, hG, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wp, complex_div_pow_div_div_pow _ _ _ _ hk, hP, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wpd, complex_div_pow_div_div_pow _ _ _ _ hk, hD, mul_pow, inv_mul_eq_div, div_div, mul_comm]

end GlobalTheory.WpFam.TauVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTauStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  first | exact @GlobalTheory.WpFam.TauVal.main | exact GlobalTheory.WpFam.TauVal.main | (intros; apply GlobalTheory.WpFam.TauVal.main <;> assumption)
end
end
