module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTauStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionMatrixOfConjugateTransportStatement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdeleTranslateIntegralAdditiveTotalPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeQuotientCorrespondenceOfTorsionTransporStatement
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGEis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRepsTransport

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem kerReps_transport : ∀ (K : Type) [Field K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (a : K) (S : Finset ℂ), IsTr ι Λ₀ Λ₁ T → a ≠ 0 → (∀ x x', T x x' → T (a * x) (a * x')) → IsKerReps Λ₀ (ι a) S → ∃ (φ : ℂ → ℂ) (S' : Finset ℂ), IsKerReps Λ₁ (ι a) S' ∧ Set.BijOn φ S S' ∧ ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ ι k' = φ P ∧ T k k' := by
  intro K _ ι Λ₀ Λ₁ T a S hT ha hmul hS
  classical
  have hιa : ι a ≠ 0 := (map_ne_zero ι).mpr ha
  obtain ⟨hS1, hS2, hS3⟩ := hS

  have hex : ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ T k k' := by
    intro P hP
    obtain ⟨b, hb⟩ := hT.rat₀ _ (hS1 P hP).1
    obtain ⟨k', hk'⟩ := hT.left (b / a)
    refine ⟨b / a, k', ?_, hk'⟩
    rw [map_div₀, hb]; field_simp
  choose! k k' hk hT' using hex
  set φ : ℂ → ℂ := fun P => ι (k' P) with hφ

  have himg : ∀ P ∈ S, ι a * φ P ∈ Λ₁.lattice ∧ φ P ∉ Λ₁.lattice := by
    intro P hP
    have h1 := hT.mem_iff _ _ (hmul _ _ (hT' P hP))
    have h2 := hT.mem_iff _ _ (hT' P hP)
    rw [map_mul, map_mul, hk P hP] at h1
    rw [hk P hP] at h2
    exact ⟨h1.mp (hS1 P hP).1, fun h => (hS1 P hP).2 (h2.mpr h)⟩
  have hdiff : ∀ P ∈ S, ∀ Q ∈ S, φ P - φ Q ∈ Λ₁.lattice → P = Q := by
    intro P hP Q hQ h
    have h1 := hT.mem_iff _ _ (hT.sub _ _ _ _ (hT' P hP) (hT' Q hQ))
    rw [map_sub, map_sub, hk P hP, hk Q hQ] at h1
    exact hS2 P hP Q hQ (h1.mpr h)
  refine ⟨φ, S.image φ, ⟨?_, ?_, ?_⟩, ⟨fun P hP => Finset.mem_coe.mpr (Finset.mem_image_of_mem φ hP),
    fun P hP Q hQ h => hdiff P hP Q hQ (by rw [h, sub_self]; exact zero_mem _), ?_⟩, ?_⟩
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    exact himg P hP
  · intro P' hP' Q' hQ' h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hQ'
    rw [hdiff P hP Q hQ h]
  · intro z hz hz'
    obtain ⟨c, hc⟩ := hT.rat₁ _ hz
    have hzc : ι (c / a) = z := by rw [map_div₀, hc]; field_simp
    obtain ⟨m, hm⟩ := hT.right (c / a)
    have h1 := hT.mem_iff _ _ (hmul _ _ hm)
    have h2 := hT.mem_iff _ _ hm
    rw [map_mul, map_mul, hzc] at h1
    rw [hzc] at h2
    obtain ⟨P, hP, hmP⟩ := hS3 (ι m) (h1.mpr hz) (fun h => hz' (h2.mp h))
    refine ⟨φ P, Finset.mem_image_of_mem φ hP, ?_⟩
    have h3 := hT.mem_iff _ _ (hT.sub _ _ _ _ hm (hT' P hP))
    rw [map_sub, map_sub, hk P hP, hzc] at h3
    exact h3.mp hmP
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hP')
    exact ⟨P, hP, rfl⟩
  · intro P hP
    exact ⟨k P, k' P, hk P hP, rfl, hT' P hP⟩

end GlobalTheory.WpFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportSecondEisensteinCm

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.NormSqOfSquareEqNeg

theorem normSq_of_sq_eq_neg (d : ℕ) (α : ℂ) (h : α ^ 2 = -(d : ℂ)) : (Complex.normSq α : ℂ) = d := by
  have h1 : Complex.normSq α ^ 2 = (d : ℝ) ^ 2 := by
    rw [← map_pow, h, Complex.normSq_neg, Complex.normSq_natCast]
    ring
  have h2 : Complex.normSq α = d := by
    have := Complex.normSq_nonneg α
    nlinarith [sq_nonneg (Complex.normSq α - d), sq_nonneg (Complex.normSq α + d), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  rw [h2]; simp

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ)
    (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ →
    g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  intro K _ _ d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT
  obtain ⟨_, _, _, hL₀, ⟨𝔞, _, hL₁⟩, _, _, hP⟩ := id hT
  obtain ⟨_, hm₀, him, hint⟩ := GlobalTheory.LatOfMult.main K d δ ι 1 Λ₀ hd hδ hL₀
  obtain ⟨_, hm₁, _, _⟩ := GlobalTheory.LatOfMult.main K d δ ι 𝔞 Λ₁ hd hδ hL₁
  have hα : ι δ ≠ 0 := fun h => him (by simp [h])
  have hδ0 : δ ≠ 0 := fun h => hα (by simp [h])
  have hα2 : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hN : (Complex.normSq (ι δ) : ℂ) = d := normSq_of_sq_eq_neg d _ hα2
  have hc : ι δ ^ 2 - (Complex.normSq (ι δ) : ℂ) = -(2 * d : ℂ) := by rw [hα2, hN]; ring
  have hc0 : -(2 * d : ℂ) ≠ 0 := by
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simpa using this
  obtain ⟨S, hS⟩ := kernel_reps_exist Λ₀ (ι δ) hα hm₀
  have hTr := GlobalTheory.T.isLatticeQuotientCorrespondence_of_torsionTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  have hmul : ∀ x x', Tr t x x' → Tr t (δ * x) (δ * x') := fun x x' h => (GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t).2.1 δ x x' hint h
  obtain ⟨φ, S', hS', hbij, hrel⟩ := GlobalTheory.WpFam.kerReps_transport K ι Λ₀ Λ₁ (Tr t) δ S hTr hδ0 hmul hS
  have e₀ := quasiPeriodConstIsogeny_thm Λ₀ (ι δ) S hα hm₀ hS
  have e₁ := quasiPeriodConstIsogeny_thm Λ₁ (ι δ) S' hα hm₁ hS'
  rw [hc] at e₀ e₁
  have s₀ : s2 Λ₀ = (∑ P ∈ S, Λ₀.weierstrassP P) / -(2 * d : ℂ) := by
    rw [eq_div_iff hc0, mul_comm, e₀]
  have s₁ : s2 Λ₁ = (∑ P ∈ S', Λ₁.weierstrassP P) / -(2 * d : ℂ) := by
    rw [eq_div_iff hc0, mul_comm, e₁]
  have key : ∀ P ∈ S, g (Λ₀.weierstrassP P / Ω₀ ^ 2) = Λ₁.weierstrassP (φ P) / Ω₁ ^ 2 := by
    intro P hPS
    obtain ⟨k, k', hk, hk', hkk⟩ := hrel P hPS
    have hnot : ι k ∉ Λ₀.lattice := by rw [hk]; exact (hS.1 P hPS).2
    have := (hP k k' hnot hkk).1
    rwa [hk, hk'] at this
  have hsum : ∑ P ∈ S, Λ₁.weierstrassP (φ P) / Ω₁ ^ 2 = ∑ Q ∈ S', Λ₁.weierstrassP Q / Ω₁ ^ 2 :=
    Finset.sum_nbij φ (fun a ha => hbij.mapsTo ha) hbij.injOn hbij.surjOn (fun _ _ => rfl)
  have hg2 : g (-(2 * d : ℂ)) = -(2 * d : ℂ) := by simp [map_neg, map_mul, map_ofNat, map_natCast]

  rw [s₀, s₁, div_right_comm, div_right_comm (∑ P ∈ S', _), map_div₀, hg2, Finset.sum_div, Finset.sum_div, map_sum,
  Finset.sum_congr rfl key, hsum]

end GlobalTheory.NormSqOfSquareEqNeg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportSecondEisensteinCmStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.galois_transport_second_eisenstein_cm : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  first | exact @GlobalTheory.NormSqOfSquareEqNeg.main | exact GlobalTheory.NormSqOfSquareEqNeg.main | (intros; apply GlobalTheory.NormSqOfSquareEqNeg.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEisensteinDivPeriod

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem E₄_div_period_eq {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₄ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 4 = 12 * (Λ.g₂ / Ω ^ 4) := by
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 4 = 16 * (Real.pi : ℂ) ^ 4 := by
    rw [mul_pow, Complex.I_pow_four]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₂_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem E₆_div_period_eq {Λ : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf Λ c τ) (Ω : ℂ) :
    E₆ τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 6 = -(216 * (Λ.g₃ / Ω ^ 6)) := by
  have h6 : Complex.I ^ 6 = -1 := by
    rw [show 6 = 4 + 2 from rfl, pow_add, Complex.I_pow_four, Complex.I_sq, one_mul]
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ^ 6 = -(64 * (Real.pi : ℂ) ^ 6) := by
    rw [mul_pow, h6]; ring
  rw [ReciprocityTheory.ChartRestriction.L1.g₃_eq h, div_pow, hI, div_div_eq_mul_div, mul_pow]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem map_E₄_div_period (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4) :
    g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4)
      = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 := by
  rw [E₄_div_period_eq h₀, E₄_div_period_eq h₁, map_mul, h, map_ofNat]

theorem map_E₆_div_period (g : ℂ ≃+* ℂ) {Λ₀ Λ₁ : PeriodPair} {c₀ c₁ Ω₀ Ω₁ : ℂ} {τ₀ τ₁ : ℍ}
    (h₀ : IsTauOf Λ₀ c₀ τ₀) (h₁ : IsTauOf Λ₁ c₁ τ₁)
    (h : g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6) :
    g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6)
      = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 := by
  rw [E₆_div_period_eq h₀, E₆_div_period_eq h₁, map_neg, map_mul, h, map_ofNat]

theorem map_eisenstein_div_period :
    ∀ (g : ℂ ≃+* ℂ) (Λ₀ Λ₁ : PeriodPair) (c₀ c₁ Ω₀ Ω₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → g (Λ₀.g₂ / Ω₀ ^ 4) = Λ₁.g₂ / Ω₁ ^ 4 → g (Λ₀.g₃ / Ω₀ ^ 6) = Λ₁.g₃ / Ω₁ ^ 6 → g (E₄ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 4) = E₄ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 4 ∧ g (E₆ τ₀ / (Ω₀ * c₀ / (2 * Real.pi * Complex.I)) ^ 6) = E₆ τ₁ / (Ω₁ * c₁ / (2 * Real.pi * Complex.I)) ^ 6 :=
  fun g _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃ =>
    ⟨map_E₄_div_period g h₀ h₁ h₂, map_E₆_div_period g h₀ h₁ h₃⟩

end GlobalTheory.QFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassTorsionConjTransport

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.Transp

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ ω₀ ω₁ : ℂ, ω₀ = Ω₀ * c₀ / (2 * Real.pi * Complex.I) → ω₁ = Ω₁ * c₁ / (2 * Real.pi * Complex.I) → ω₀ ≠ 0 ∧ ω₁ ≠ 0 ∧ g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 ∧ g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 ∧ g (G2s τ₀ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₀ ^ 2) = G2s τ₁ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₁ ^ 2 ∧ ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), (∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') ∧ ∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3 := by
  intro K _ _ d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT c₀ c₁ τ₀ τ₁ h₀ h₁ ω₀ ω₁ hω₀ hω₁
  subst hω₀ hω₁
  have hT' := hT
  obtain ⟨hΩ₀, hΩ₁, -, -, -, hg₂, hg₃, hwp⟩ := hT'
  have h2πi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have hE := map_eisenstein_div_period g Λ₀ Λ₁ c₀ c₁ Ω₀ Ω₁ τ₀ τ₁ h₀ h₁ hg₂ hg₃
  have hs₀ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ₀ c₀ Ω₀ τ₀ h₀
  have hs₁ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ₁ c₁ Ω₁ τ₁ h₁
  have hs := GlobalTheory.T.galois_transport_second_eisenstein_cm K d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT
  refine ⟨div_ne_zero (mul_ne_zero hΩ₀ h₀.1) h2πi, div_ne_zero (mul_ne_zero hΩ₁ h₁.1) h2πi,
    hE.1, hE.2, ?_, ?_⟩
  · rw [hs₀.1, hs₁.1, hs]
  · intro N _
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_torsion_matrix_of_conjugateTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT c₀ c₁ τ₀ τ₁ h₀ h₁ N
    refine ⟨A, hA, fun x => ?_⟩
    rw [(hs₀.2 N x).1, (hs₀.2 N x).2, (hs₁.2 N (vmul x A)).1, (hs₁.2 N (vmul x A)).2]
    by_cases hx : x = 0
    · have hv : vmul x A = 0 := ((GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x A).2 hx
      have ht : ∀ τ : ℍ, tors N τ 0 = 0 := by intro τ; simp [tors]
      rw [hv, hx, ht, ht, mul_zero, mul_zero]
      simp [PeriodPair.weierstrassP_zero, PeriodPair.derivWeierstrassP_zero]
    · obtain ⟨k, k', hk, hk', htr⟩ := hA x
      have hnot : ι k ∉ Λ₀.lattice := by
        rw [hk, ((GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ₀ c₀ τ₀ h₀).1 _), ((GlobalTheory.WpFam.TorsMem.main N τ₀).2.2.1 x)]
        exact hx
      rw [← hk, ← hk']
      exact hwp k k' hnot htr

end GlobalTheory.WpFam.Transp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassTorsionConjTransportStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.eisenstein_weierstrass_torsion_conj_transport : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ ω₀ ω₁ : ℂ, ω₀ = Ω₀ * c₀ / (2 * Real.pi * Complex.I) → ω₁ = Ω₁ * c₁ / (2 * Real.pi * Complex.I) → ω₀ ≠ 0 ∧ ω₁ ≠ 0 ∧ g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 ∧ g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 ∧ g (G2s τ₀ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₀ ^ 2) = G2s τ₁ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₁ ^ 2 ∧ ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), (∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') ∧ ∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3 := by
  first | exact @GlobalTheory.WpFam.Transp.main | exact GlobalTheory.WpFam.Transp.main | (intros; apply GlobalTheory.WpFam.Transp.main <;> assumption)
end
end
