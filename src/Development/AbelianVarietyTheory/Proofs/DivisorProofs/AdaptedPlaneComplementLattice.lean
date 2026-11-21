module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeComapMulVecLinOfLeftInverseMatrix

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory

theorem isLattice_complement_of_adapted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ P : Matrix (Fin n₁) (Fin n) E, P * H.ι = 1 → W₁.L.IsLattice E := by
  intro F E _ _ _ _ _ σ B _ n n₁ W W₁ H i₀ i₁ r s hW hH P hP
  have hL : W₁.L = W.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := by
    ext u
    rw [hH.low u]
    rfl
  rw [hL]
  set f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) :=
    (Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)
  set g : (Fin n → E) →ₗ[𝓞 E] (Fin n₁ → E) :=
    (Matrix.mulVecLin P).restrictScalars (𝓞 E)
  have hgf : ∀ u, g (f u) = u := by
    intro u
    simp [f, g, Matrix.mulVec_mulVec, hP]
  have hN : IsNoetherian (𝓞 E) W.L := isNoetherian_of_fg_of_noetherian W.L hW.lat.fg
  have h1 : ((W.L.comap f).map f).FG :=
    isNoetherian_submodule.1 hN _ (Submodule.map_comap_le f W.L)
  have h2 : ((W.L.comap f).map f).map g = W.L.comap f := by
    rw [← Submodule.map_comp]
    ext u
    simp only [Submodule.mem_map, LinearMap.coe_comp, Function.comp_apply, hgf]
    exact ⟨fun ⟨v, hv, he⟩ => he ▸ hv, fun hu => ⟨u, hu, rfl⟩⟩
  apply Submodule.IsLattice.of_fg E
  rw [← h2]
  exact h1.map g

end GlobalTheory
