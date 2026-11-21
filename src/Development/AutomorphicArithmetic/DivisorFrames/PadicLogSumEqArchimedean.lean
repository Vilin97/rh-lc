module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicProductFormula

@[expose] public section

open NumberField

private theorem sum_log_emb (F : Type) [Field F] [NumberField F] (N : F) (hN : N ≠ 0) :
    ∑ σ : F →+* ℂ, Real.log ‖σ N‖ = Real.log ((|Algebra.norm ℚ N| : ℚ) : ℝ) := by
  have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ N)
  simp only [norm_prod] at h
  rw [← Real.log_prod (fun σ _ => by simpa using hN)]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun σ : F →+* ℂ => ‖σ N‖)
    (fun σ : F →ₐ[ℚ] ℂ => ‖σ N‖) (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
  simp [← Complex.norm_ratCast]
