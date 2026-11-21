module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sUnits_over_and_conj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → (∀ x : Fˣ, Units.map (algebraMap F E : F →* E) x ∈ sUnits E SE ↔ x ∈ sUnits F S) ∧ ∀ y : Eˣ, y ∈ sUnits E SE → Units.map (σ : E →* E) y ∈ sUnits E SE := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hS
  have hplaces :
      (∀ S : Finset (HeightOneSpectrum (𝓞 F)),
        ∃ SE : Finset (HeightOneSpectrum (𝓞 E)),
          ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧
      ∀ w : HeightOneSpectrum (𝓞 E),
        ∃ e : ℕ, 0 < e ∧ ∀ x : F,
          w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by
    refine ⟨fun S => ?_, fun v => ?_, fun w => ?_⟩
    · have hfin : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S}.Finite := by
        have hU : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S} =
            ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v} := by
          ext w
          simp
        rw [hU]
        exact S.finite_toSet.biUnion fun v _ => by
          refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).preimage
            (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
          rintro w rfl
          exact ⟨w.isPrime, ⟨rfl⟩⟩
      exact ⟨hfin.toFinset, fun w => by simp⟩
    · obtain ⟨P, hmax, hover⟩ :=
        Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal (S := 𝓞 E)
      have hne : P ≠ ⊥ := by
        rintro rfl
        apply v.ne_bot
        rw [hover.over]
        exact Ideal.comap_bot_of_injective _
          (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
      exact ⟨⟨P, hmax.isPrime, hne⟩, HeightOneSpectrum.ext hover.over.symm⟩
    · have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
      refine ⟨(w.under (𝓞 F)).asIdeal.ramificationIdx' w.asIdeal,
        Nat.pos_of_ne_zero ?_, fun x => ?_⟩
      · refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ w.isPrime
          Ideal.map_comap_le
        rw [Ne, Ideal.map_eq_bot_iff_of_injective
          (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
        exact (w.under (𝓞 F)).ne_bot
      · rw [Ideal.ramificationIdx'_eq_ramificationIdx
          (w.under (𝓞 F)).asIdeal w.asIdeal (w.under (𝓞 F)).ne_bot]
        exact (HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 F)) w x).symm
  obtain ⟨-, hup, hval⟩ := hplaces
  obtain ⟨hconj, -⟩ := conj_places_transitive F E δ θ σ hq
  refine ⟨fun x => ⟨fun h => ?_, fun h => ?_⟩, fun y hy => ?_⟩
  · rw [mem_sUnits] at h ⊢
    intro v hv
    obtain ⟨w, rfl⟩ := hup v
    obtain ⟨e, he, hx⟩ := hval w
    have h1 : w.valuation E (algebraMap F E (x : F)) = 1 := h w (fun a => hv ((hS w).1 a))
    rw [hx] at h1
    exact (pow_eq_one_iff_of_nonneg zero_le he.ne').1 h1
  · rw [mem_sUnits] at h ⊢
    intro w hw
    obtain ⟨e, he, hx⟩ := hval w
    change w.valuation E (algebraMap F E (x : F)) = 1
    rw [hx, h _ (fun a => hw ((hS w).2 a)), one_pow]
  · rw [mem_sUnits] at hy ⊢
    intro w hw
    obtain ⟨w', hu, hv⟩ := hconj w
    change w.valuation E (σ (y : E)) = 1
    rw [← hv]
    exact hy w' (fun a => hw ((hS w).2 (hu ▸ (hS w').1 a)))

end GlobalTheory.QNorm
