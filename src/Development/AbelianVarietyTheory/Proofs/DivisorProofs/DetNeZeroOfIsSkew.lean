module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.TorusCentre

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_zero_of_isSkew {B : Base F E} {d₁ : ℕ} {W₁ : Spc F E d₁} {r s : ℕ} (h : W₁.IsSkew σ B r s) :
    W₁.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := h.sig w
  set φ := (B.emb w).1
  let e : Fin r ⊕ Fin s ≃ Fin d₁ := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin d₁) (Fin d₁) ℂ := A.submatrix id e.symm
  have h2 : A'ᵀ * (Complex.I • W₁.J.map φ) * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.submatrix, Matrix.transpose_apply]
  have hD : ((Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm).det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  rw [← h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_smul] at hD
  intro h0
  apply hD
  have : (W₁.J.map φ).det = φ W₁.J.det := by
    simp [RingHom.map_det]
  rw [this, h0]
  simp

section Adapted

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ : ℕ}

end Adapted

section Gen

variable {R : Type} [CommRing R] (c : R →+* R) {d d₁ : ℕ} {J : Matrix (Fin d) (Fin d) R} {I : Matrix (Fin d) (Fin d₁) R}
  {J₁ : Matrix (Fin d₁) (Fin d₁) R} {X Y : Fin d → R}

end Gen

section Transfer

end Transfer

section Decomp

variable {R : Type} [CommRing R] {d d₁ : ℕ} {I : Matrix (Fin d) (Fin d₁) R} {X Y : Fin d → R}

end Decomp

section Span

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ : ℕ}

end Span

section Group

variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}

end Group

section Step

variable {B : Base F E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁} {i₀ i₁ : ℕ}

end Step

section Pow

variable {R : Type} [CommRing R] {d : ℕ}

end Pow

end GlobalTheory.ThK.TorusCentre
