module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose

@[expose] public section

open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeo


open scoped ComplexOrder in
theorem specpos_inv_eigenvalues (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε)
    (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) :
    (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) := by
  have hmul : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) = 1
    simp
  have hinj : Function.Injective (S7.toM g⁻¹).mulVec := by
    intro x y hxy
    have h := congrArg (S7.toM g).mulVec hxy
    simpa [Matrix.mulVec_mulVec, hmul] using h
  have hpd : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self _ hinj
  refine ⟨fun i => hpd.eigenvalues_pos i, ?_⟩
  have htr := hT.trace_eq_sum_eigenvalues
  have hre : ∑ i, hT.eigenvalues i = (Matrix.trace ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹)).re := by
    rw [htr]
    simp
  have hs_ct (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs Mᴴ = Formalism.REAL.hs M := by
    simp only [Formalism.REAL.hs, Matrix.conjTranspose_apply, norm_star]
    exact Finset.sum_comm
  have hs_j_left (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs (Formalism.REAL.Jm ε * M) = Formalism.REAL.hs M := by
    have h : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
    simp only [Formalism.REAL.hs, Formalism.REAL.Jm, Matrix.diagonal_mul, norm_mul, h, one_mul]
  have hs_j_right (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs (M * Formalism.REAL.Jm ε) = Formalism.REAL.hs M := by
    rw [← hs_ct, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose, hs_j_left, hs_ct]
  have hs_trace (M : Matrix (Fin n) (Fin n) ℂ) :
      Formalism.REAL.hs M = (Matrix.trace (M * Mᴴ)).re := by
    simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e : M i j * star (M i j) = ((‖M i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e, Complex.ofReal_re]
  have hhs : Formalism.REAL.hs (S7.toM g⁻¹) = Formalism.REAL.hs (S7.toM g) := by
    rw [S7.toM_inv]
    show Formalism.REAL.hs (Formalism.REAL.Jm ε * (S7.toM g)ᴴ * Formalism.REAL.Jm ε) = _
    rw [hs_j_right, hs_j_left, hs_ct]
  rw [hre, ← hhs]
  simpa only [conjTranspose_conjTranspose, hs_ct] using
    (hs_trace (S7.toM g⁻¹)ᴴ).symm

end GlobalTheory.CompanionTheory.UGeo
