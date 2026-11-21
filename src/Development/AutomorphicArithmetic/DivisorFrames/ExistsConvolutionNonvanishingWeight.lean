module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsTestFourierNonvanishing
public import Development.AutomorphicArithmetic.DivisorFrames.FourierNonvanishingUnitPoint
public import Development.AutomorphicArithmetic.DivisorFrames.FourierContinuousNonvanishing
public import Development.AutomorphicArithmetic.DivisorFrames.ConvolutionDecayIntegrableFourier

@[expose] public section

open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

private theorem bound_int {ι : Type} [Fintype ι] (C : ℝ) :
    Integrable (fun s : ι → ℂ => C / (1 + ‖s‖) ^ (Module.finrank ℝ (ι → ℂ) + 1)) := by
  have := integrable_one_add_norm (E := ι → ℂ) (μ := volume)
    (r := ((Module.finrank ℝ (ι → ℂ) + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  refine (this.const_mul C).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]
