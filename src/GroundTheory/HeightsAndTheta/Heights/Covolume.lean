module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
public import GroundTheory.HeightsAndTheta.Heights.HermitianEuclidean
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact

@[expose] public section

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module

open scoped Kronecker

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

section Real

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E)

namespace RealSpace

end RealSpace

end Real


theorem det_basisMatrix_sq : (basisMatrix K).det ^ 2 = ((discr K : ℤ) : ℂ) := by
  rw [basisMatrix_eq_embeddingsMatrixReindex,
    ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (integralBasis K ∘ (equivReindex K)) (RingHom.equivRatAlgHom K ℂ),
    ← (equivReindex K).symm_symm, Algebra.discr_reindex ℚ (integralBasis K) (equivReindex K).symm,
    ← coe_discr]
  simp

theorem basisMatrix_apply' (τ σ : K →+* ℂ) :
    basisMatrix K τ σ = σ ((RingOfIntegers.basis K (equivReindex K τ) : 𝓞 K) : K) := by
  simp [basisMatrix, canonicalEmbedding.latticeBasis_apply, integralBasis_apply,
    canonicalEmbedding.apply_at]

section Gram

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]

end Gram

section RiemannRoch

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]
  {s : ι → E}



end RiemannRoch

namespace HermitianExtension

variable {E' E E'' : HermitianBundle K} (X : HermitianExtension E' E E'')

end HermitianExtension

end

end GroundTheory.Heights₂.Heights
