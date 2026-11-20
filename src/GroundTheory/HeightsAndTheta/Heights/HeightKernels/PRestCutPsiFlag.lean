import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutPsiFlag.proof : RestCutPsiFlag.Statement := by
  intro f N
  refine ⟨fun H => ?_, fun ψ P => ?_⟩
  · unfold realFlagIntegral RestTerms.flagIntegral
    push_cast [Rat.cast_sum, Rat.cast_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [coeff_map, eq_ratCast]
    ring
  · unfold realFlagIntegral RestTerms.flagIntegral
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [KRest.coeff_psiPoly]
    have h : AddMonoidAlgebra.coeff P α * ((AddMonoidAlgebra.coeff (RestTerms.blockVandermonde f N) α *
        α.prod (fun _ e => (e.factorial : ℚ)) : ℚ) : ℝ) =
        (AddMonoidAlgebra.coeff (RestTerms.blockVandermonde f N) α *
          α.prod (fun _ e => (e.factorial : ℚ))) • AddMonoidAlgebra.coeff P α := by
      rw [Rat.smul_def, mul_comm]
    rw [h, ψ.map_smul, smul_eq_mul]
    ring

end GroundTheory.Heights₂.Heights
