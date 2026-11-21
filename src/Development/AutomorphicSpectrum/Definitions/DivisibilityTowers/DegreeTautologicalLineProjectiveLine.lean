import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.Top.Model

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_pk_mul (τ : Ψ) (k : ℕ) (hk : 1 ≤ k) (Q : RP Ψ N) : degFl (pk τ k * Q) = 0 :=
  Formalism.DegreeFormula.degreePowerSumMulEqZero Ψ N τ k Q hk

theorem degFl_add (P Q : RP Ψ N) : degFl (P + Q) = degFl P + degFl Q := by
  simp only [degFl, MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.CompanionTheory.Ar.Top.Model
