module

public import Mathlib
public import Formalism.DegreeFormula.PointDegree.PowSum
public import Formalism.DegreeFormula.PointDegree.PermExpInj
public import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

@[expose] public section

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory

theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open {σ : Type*} [Fintype σ]
    {U : Set (σ → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) (p : MvPolynomial σ ℝ)
    (hp : ∀ x ∈ U, eval x p = 0) : p = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 hU x hx
  refine MvPolynomial.funext_set (fun i => Set.Ioo (x i - ε) (x i + ε))
    (fun i => Set.Ioo_infinite (by linarith)) fun y hy => ?_
  rw [map_zero]
  refine hp y (hb ?_)
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  have := hy i (Set.mem_univ i)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [this.1, this.2]

end GlobalTheory
