module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

private theorem kill_fin {V Y S : Type} [AddCommGroup V] [Module ℂ V] [TopologicalSpace Y] (N : Submodule ℂ V)
    (ι : V →ₗ[ℂ] (Y → ℂ)) (hι : Set.BijOn ι (N : Set V) (SB Y : Set _)) (L : V →ₗ[ℂ] ℂ) (χ : S → Y → ℂ)
    (hχ : ∀ s, IsLocallyConstant (χ s))
    (hL : ∀ s, ∀ φ ∈ N, ∃ φ₁ ∈ N, L φ₁ = L φ ∧ ∀ y, ι φ₁ y = χ s y * ι φ y) (T : Finset S) :
    ∀ φ ∈ N, (∀ y, ι φ y ≠ 0 → ∃ s ∈ T, χ s y ≠ 1) → L φ = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro φ hφ h
    have h0 : ι φ = ι 0 := by
      rw [map_zero]; funext y; by_contra hy; simpa using h y hy
    rw [hι.injOn hφ N.zero_mem h0, map_zero]
  | insert s T _ ih =>
    intro φ hφ h
    have hf : ι φ ∈ SB Y := hι.mapsTo hφ
    have hg : (fun y => (χ s y - 1)⁻¹ * ι φ y) ∈ SB Y :=
      ⟨((hχ s).comp fun z => (z - 1)⁻¹).mul hf.1, hf.2.mul_left⟩
    obtain ⟨g, hgN, hge⟩ := hι.surjOn hg
    obtain ⟨g₁, hg₁, e1, e2⟩ := hL s g hgN
    have := ih (φ - (g₁ - g)) (N.sub_mem hφ (N.sub_mem hg₁ hgN)) fun y hy => by
      simp only [map_sub, Pi.sub_apply, e2, hge] at hy
      by_cases hs : χ s y = 1
      · have hy' : ι φ y ≠ 0 := by simpa [hs] using hy
        obtain ⟨s', hs', h'⟩ := h y hy'
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd hs h'
        · exact ⟨s', hs', h'⟩
      · exfalso
        have := sub_ne_zero.2 hs
        apply hy
        field_simp
        ring
    simpa [map_sub, e1] using this

private theorem kill {V Y S : Type} [AddCommGroup V] [Module ℂ V] [TopologicalSpace Y] (N : Submodule ℂ V)
    (ι : V →ₗ[ℂ] (Y → ℂ)) (hι : Set.BijOn ι (N : Set V) (SB Y : Set _)) (L : V →ₗ[ℂ] ℂ) (χ : S → Y → ℂ)
    (hχ : ∀ s, IsLocallyConstant (χ s))
    (hL : ∀ s, ∀ φ ∈ N, ∃ φ₁ ∈ N, L φ₁ = L φ ∧ ∀ y, ι φ₁ y = χ s y * ι φ y) :
    ∀ φ ∈ N, (∀ y, ι φ y ≠ 0 → ∃ s, χ s y ≠ 1) → L φ = 0 := by
  intro φ hφ h
  have hf : ι φ ∈ SB Y := hι.mapsTo hφ
  have hcl : IsClosed (Function.support (ι φ)) := ((IsLocallyConstant.iff_isOpen_fiber.1 hf.1 0).isClosed_compl)
  have hc : IsCompact (Function.support (ι φ)) := hf.2.isCompact.of_isClosed_subset hcl (subset_tsupport _)
  obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun s => {y | χ s y ≠ 1}) (fun s => hχ s {z | z ≠ 1})
    (fun y hy => Set.mem_iUnion.2 (h y hy))
  refine kill_fin N ι hι L χ hχ hL T φ hφ fun y hy => ?_
  simpa using hT hy

private theorem cont_pair {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n d : ℕ} (p : Fin n → K)
    (q : Fin d → K) : Continuous fun Y : Matrix (Fin n) (Fin d) K => -((p ᵥ* Y) ⬝ᵥ q) := by
  simp only [Matrix.vecMul, dotProduct]
  fun_prop
