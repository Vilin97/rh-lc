import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem exists_rep {ι : Type} [Fintype ι] (l : (ι → ℂ) →ₗ[ℝ] ℝ) :
    ∃ y : ι → ℂ, ∀ s : ι → ℂ, l s = (∑ w, (s * y) w).re := by
  classical
  refine ⟨fun w => (l (Pi.single w 1) : ℂ) - (l (Pi.single w Complex.I) : ℂ) * Complex.I, fun s => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single s]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (Pi.single w (s w) : ι → ℂ) =
      (s w).re • (Pi.single w 1 : ι → ℂ) + (s w).im • (Pi.single w Complex.I : ι → ℂ) := by
    rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
    congr 1
    simp
  rw [h, map_add (f := _), map_smul, map_smul]
  simp

private theorem continuous_FT {ι : Type} [Fintype ι] (φ : (ι → ℂ) → ℂ) (hc : Continuous φ)
    (hi : Integrable φ) : Continuous (FT φ) := by
  unfold FT
  refine continuous_of_dominated (bound := fun s => ‖φ s‖) (fun y => ?_) (fun y => ?_) hi.norm ?_
  · exact (hc.mul (continuous_ec.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s => by rw [norm_mul, norm_ec, mul_one]
  · exact Filter.Eventually.of_forall fun s =>
      continuous_const.mul (continuous_ec.comp (continuous_const.mul continuous_id))

open FourierTransform in
