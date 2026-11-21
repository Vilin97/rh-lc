import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
import Development.AutomorphicArithmetic.DivisorFrames.ExistsTestFourierNonvanishing
import Development.AutomorphicArithmetic.DivisorFrames.FourierNonvanishingUnitPoint
import Development.AutomorphicArithmetic.DivisorFrames.FourierContinuousNonvanishing
import Development.AutomorphicArithmetic.DivisorFrames.ConvolutionDecayIntegrableFourier
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem bound_int {ι : Type} [Fintype ι] (C : ℝ) :
    Integrable (fun s : ι → ℂ => C / (1 + ‖s‖) ^ (Module.finrank ℝ (ι → ℂ) + 1)) := by
  have := integrable_one_add_norm (E := ι → ℂ) (μ := volume)
    (r := ((Module.finrank ℝ (ι → ℂ) + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  refine (this.const_mul C).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]
