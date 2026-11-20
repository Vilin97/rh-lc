import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumPowMulFactorial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_sum_pow_mul_factorial : ∀ {σ : Type} [DecidableEq σ] (C R : Finset σ) (k : ℕ) (ω : MvPolynomial σ ℝ), AddMonoidAlgebra.coeff ((∑ s ∈ C, X s) ^ k * ω) (mono R) = (k.factorial : ℝ) * ∑ U ∈ (R ∩ C).powersetCard k, AddMonoidAlgebra.coeff ω (mono (R \ U)) := by
  first | exact @GlobalTheory.MultinomCoeff.coeff_mono_sum_pow_mul | exact GlobalTheory.MultinomCoeff.coeff_mono_sum_pow_mul | (intros; apply GlobalTheory.MultinomCoeff.coeff_mono_sum_pow_mul <;> assumption)
