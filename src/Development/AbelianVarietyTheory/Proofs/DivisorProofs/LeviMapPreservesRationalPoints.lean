module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLift

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviRatHerm

open Matrix GlobalTheory.LeviElem GlobalTheory.LeviRat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem decomp {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} (hlat : Submodule.IsLattice E W.L)
    {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    (∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + b • H'.y) ∧
    ∀ u : Fin d₁ → E, H'.ι *ᵥ u = 0 → u = 0 := by
  let φ : ((E × (Fin d₁ → E)) × E) →ₗ[E] (Fin d → E) :=
    LinearMap.coprod (LinearMap.coprod (LinearMap.toSpanSingleton E _ H'.x) (Matrix.mulVecLin H'.ι))
      (LinearMap.toSpanSingleton E _ H'.y)
  have hφ : ∀ p, φ p = p.1.1 • H'.x + H'.ι *ᵥ p.1.2 + p.2 • H'.y := fun p => by
    simp [φ, LinearMap.coprod_apply]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hlat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hA.split z hz
    exact ⟨((a, u), b), hφ _⟩
  have hrk : Module.finrank E ((E × (Fin d₁ → E)) × E) = Module.finrank E (Fin d → E) := by
    simp [Module.finrank_prod, hA.rank]; ring
  have hinj : Function.Injective φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).2 hsurj
  refine ⟨fun v => ?_, fun u hu => ?_⟩
  · obtain ⟨p, rfl⟩ := hsurj v
    exact ⟨p.1.1, p.2, p.1.2, hφ p⟩
  · have : φ ((0, u), 0) = φ 0 := by rw [hφ, map_zero]; simp [hu]
    have := hinj this
    simpa using congrArg (fun p => p.1.2) this

end GlobalTheory.LeviRatHerm

namespace GlobalTheory.LeviRatHerm

open Matrix GlobalTheory.LeviElem GlobalTheory.LeviRat

end GlobalTheory.LeviRatHerm

end
