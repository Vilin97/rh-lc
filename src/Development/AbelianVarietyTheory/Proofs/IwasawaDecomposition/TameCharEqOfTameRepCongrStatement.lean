module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
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
import ReciprocityTheory.GaloisValuations.GlobalB
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharacterIndependentUniformizer

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem valuation_algebraMap_int_le_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (x : 𝓞 E) : A.valuation (algebraMap E Ω (x : E)) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap)

theorem valuation_uniformiser_le {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hP : IsPlaceOver A P) {ϖ ϖ' : 𝓞 E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal) :
    A.valuation (algebraMap E Ω (ϖ' : E)) ≤ A.valuation (algebraMap E Ω (ϖ : E)) := by
  have hdvd : P.asIdeal ∣ Ideal.span {ϖ} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ (J : Set (𝓞 E)) ⊆ P.asIdeal := by
    intro hle
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  have hmem : ϖ' * s ∈ Ideal.span {ϖ} := by
    rw [hJ]; exact Ideal.mul_mem_mul h1' hsJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hs1 : A.valuation (algebraMap E Ω (s : E)) = 1 :=
    le_antisymm (valuation_algebraMap_int_le_one A s) (not_lt.1 fun h => hsP ((hP s).1 h))
  have e : algebraMap E Ω (a : E) * algebraMap E Ω (ϖ : E) = algebraMap E Ω (ϖ' : E) * algebraMap E Ω (s : E) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact_mod_cast ha
  have hv := congrArg A.valuation e
  rw [map_mul, map_mul, hs1, mul_one] at hv
  rw [← hv]
  calc A.valuation (algebraMap E Ω (a : E)) * A.valuation (algebraMap E Ω (ϖ : E))
      ≤ 1 * A.valuation (algebraMap E Ω (ϖ : E)) := by
        gcongr; exact valuation_algebraMap_int_le_one A a
    _ = A.valuation (algebraMap E Ω (ϖ : E)) := one_mul _

theorem tame_quot_indep : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ (ϖ ϖ' : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ (π π' : Ω), π ^ m = algebraMap E Ω (ϖ : E) → π' ^ m = algebraMap E Ω (ϖ' : E) → ∀ σ ∈ Ine (F := E) A, σ π / π = σ π' / π' := by
  intro E Ω _ _ _ _ _ A P hP m hm0 hmP ϖ ϖ' h1 h2 h1' h2' π π' hπ hπ' σ hσ
  have hne : ∀ x : 𝓞 E, x ∉ P.asIdeal ^ 2 → algebraMap E Ω (x : E) ≠ 0 := by
    intro x hx h0
    apply hx
    have hx0 : (x : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).1 h0
    have : x = 0 := by exact_mod_cast hx0
    rw [this]; exact zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hne ϖ h2 (by rw [← hπ, zero_pow hm0.ne'])
  have hπ0' : π' ≠ 0 := by
    rintro rfl; exact hne ϖ' h2' (by rw [← hπ', zero_pow hm0.ne'])
  have hv : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ' : E)) :=
    le_antisymm (valuation_uniformiser_le hP h1' h2' h1) (valuation_uniformiser_le hP h1 h2 h1')
  set ρ := π' / π with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hπ0' hπ0
  have hρm : ρ ^ m = algebraMap E Ω ((ϖ' : E) / (ϖ : E)) := by
    rw [hρ, div_pow, hπ, hπ', map_div₀]
  have hvρm : A.valuation ρ ^ m = 1 := by
    rw [← Valuation.map_pow, hρm, map_div₀, map_div₀, hv, div_self]
    simpa using hne ϖ' h2'
  have hvρ : A.valuation ρ = 1 := by
    rcases lt_trichotomy (A.valuation ρ) 1 with h | h | h
    · exact absurd hvρm (pow_lt_one₀ zero_le h hm0.ne').ne
    · exact h
    · exact absurd hvρm (one_lt_pow₀ h hm0.ne').ne'
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    apply (hP _).1
    simpa using h
  have hσρm : (σ ρ / ρ) ^ m = 1 := by
    rw [div_pow, ← map_pow, hρm, AlgEquiv.commutes, ← hρm]
    exact div_self (pow_ne_zero _ hρ0)
  have hclose : A.valuation (σ ρ / ρ - 1) < 1 := by
    have e : σ ρ / ρ - 1 = (σ ρ - ρ) / ρ := by field_simp
    rw [e, map_div₀, hvρ, div_one]
    exact hσ.2 ρ hvρ.le
  have hfix : σ ρ / ρ = 1 := root_eq_of_close A m hσρm (one_pow m) hmv hclose
  have hfix' : σ ρ = ρ := (div_eq_one_iff_eq hρ0).1 hfix
  have eπ' : π' = ρ * π := by rw [hρ]; field_simp
  rw [eπ', map_mul, hfix', mul_div_mul_left _ _ hρ0]

end GlobalTheory.TameTau
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameRepConjugateInertia

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
open scoped Pointwise

namespace GlobalTheory.TameTauConj

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem conj_mem_Ine_of_mem_Ine_smul [IsAlgClosure E Ω] {A : ValuationSubring Ω} {g σ : G E Ω}
    (hσ : σ ∈ Ine (F := E) (g • A)) : g⁻¹ * σ * g ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        AlgEquiv.smul_def]
      have : (g⁻¹ : G E Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (smul_valuation_lt_one_iff g A _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G E Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ : G E Ω) (g x) = x
      show (g⁻¹ * g) x = x
      simp
    rw [e] at h
    exact h

end GlobalTheory.TameTauConj


open GlobalTheory.TameTauConj in
theorem GlobalTheory.TameTauConj.tameRep_conj : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A₀ : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A₀ P → ∀ (e : ℤ) (σ : G E Ω) (u : 𝓞 E), NX.TameRep P e σ u → ∃ ρ : G E Ω, ρ⁻¹ * σ * ρ ∈ Ine (F := E) A₀ ∧ ∃ (ϖ : 𝓞 E) (π : Ω), ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ π ^ (normV P - 1) = algebraMap E Ω (ϖ : E) ∧ A₀.valuation ((ρ⁻¹ * σ * ρ) π / π - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ A₀ P hA₀ e σ u hT
  obtain ⟨A, hA, hσ, ϖ, π, h1, h2, h3, h4⟩ := hT
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver hA₀ hA
  subst hρ
  refine ⟨ρ, conj_mem_Ine_of_mem_Ine_smul hσ, ϖ, (ρ⁻¹ : G E Ω) π, h1, h2, ?_, ?_⟩
  · rw [← map_pow, h3, AlgEquiv.commutes]
  · have e1 : (ρ⁻¹ * σ * ρ) ((ρ⁻¹ : G E Ω) π) = (ρ⁻¹ : G E Ω) (σ π) := by
      show (ρ⁻¹ * σ * ρ * ρ⁻¹) π = (ρ⁻¹ * σ) π
      rw [show ρ⁻¹ * σ * ρ * ρ⁻¹ = ρ⁻¹ * σ by group]
    have e2 : (ρ⁻¹ * σ * ρ) ((ρ⁻¹ : G E Ω) π) / (ρ⁻¹ : G E Ω) π - (algebraMap E Ω (u : E)) ^ e
        = (ρ⁻¹ : G E Ω) (σ π / π - (algebraMap E Ω (u : E)) ^ e) := by
      rw [e1, map_sub, map_div₀, map_zpow₀, AlgEquiv.commutes]
    rw [e2]
    exact (smul_valuation_lt_one_iff ρ A₀ _).1 h4
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongr

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem char_eq_of_tameRep_congr : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)), ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → 0 < normV P - 1 → ((normV P - 1 : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (normV P - 1) = 1) → ∀ (σ σ' : G E Ω) (u u' : 𝓞 E), NX.TameRep P 1 σ u → NX.TameRep P 1 σ' u' → u - u' ∈ P.asIdeal → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ P O _ _ _ _ _ hO χ hχ hm hmP hk σ σ' u u' hσ hσ' huu
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A P := exists_isPlaceOver Ω P
  obtain ⟨ρ, hs, ϖ, π, hϖ, hϖ2, hπ, hv⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ u hσ
  obtain ⟨ρ', hs', ϖ', π', hϖ', hϖ2', hπ', hv'⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ' u' hσ'
  have hconj : ∀ a b : G E Ω, χ (a⁻¹ * b * a) = χ b := by
    intro a b
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  rw [← hconj ρ σ, ← hconj ρ' σ']
  set s := ρ⁻¹ * σ * ρ
  set s' := ρ'⁻¹ * σ' * ρ'
  set m := normV P - 1
  rw [zpow_one] at hv hv'
  rw [← GlobalTheory.TameTau.tame_quot_indep A P hA m hm hmP ϖ ϖ' hϖ hϖ2 hϖ' hϖ2' π π' hπ hπ' s' hs'] at hv'
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Submodule.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  have hroot : ∀ t : G E Ω, (t π / π) ^ m = 1 := by
    intro t
    rw [div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  have hlt : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P.asIdeal := by
    intro x
    exact hA x
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hlt]
    simpa using h
  have hu : A.valuation (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) < 1 := by
    have := (hlt (u - u')).2 huu
    simpa using this
  have heq : s π / π = s' π / π := by
    refine root_eq_of_close A m (hroot s) (hroot s') hmv ?_
    have e : s π / π - s' π / π = (s π / π - algebraMap E Ω (u : E))
        + (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) - (s' π / π - algebraMap E Ω (u' : E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ (Valuation.map_add_lt _ hv hu) hv'
  exact GlobalTheory.T.continuous_char_eq_of_inertia_condition A P hA hO χ hχ m hm hmP (hk A hA) ϖ hϖ hϖ2 π hπ s hs s' hs'
    ((div_left_inj' hπ0).1 heq)

end GlobalTheory.TameTau
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongrStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

theorem _root_.GlobalTheory.T.tameChar_eq_of_tameRep_congr : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)), ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → 0 < normV P - 1 → ((normV P - 1 : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (normV P - 1) = 1) → ∀ (σ σ' : G E Ω) (u u' : 𝓞 E), NX.TameRep P 1 σ u → NX.TameRep P 1 σ' u' → u - u' ∈ P.asIdeal → χ σ = χ σ' := by
  first | exact @GlobalTheory.TameTau.char_eq_of_tameRep_congr | exact GlobalTheory.TameTau.char_eq_of_tameRep_congr | (intros; apply GlobalTheory.TameTau.char_eq_of_tameRep_congr <;> assumption)
end
end
