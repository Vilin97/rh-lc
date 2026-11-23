module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFderivLeOfBoundedGen

section

@[expose] public section

namespace GlobalTheory.FrechetDerivativeBound

theorem norm_fderiv_le_of_bounded_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} {ρ R M : ℝ} (hρ : 0 < ρ) (hR : ρ < R) (u : E → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ := by
  have hp : p ∈ Metric.ball p R := Metric.mem_ball_self (hρ.trans hR)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p hp)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM0 hρ.le) ?_
  intro v hv
  have hmem : ∀ t ∈ Metric.closedBall (0 : ℂ) ρ, p + t • v ∈ Metric.ball p R := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one]
    exact ht.trans_lt hR
  have hline : ∀ t : ℂ, HasDerivAt (fun s : ℂ => p + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hd : DifferentiableOn ℂ (fun t : ℂ => u (p + t • v)) (Metric.closedBall 0 ρ) :=
    hu.comp (fun t _ => (hline t).differentiableAt.differentiableWithinAt) hmem
  have hdc : DiffContOnCl ℂ (fun t : ℂ => u (p + t • v)) (Metric.ball 0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball _ hρ.ne']
  have hup : DifferentiableAt ℂ u p := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hp)
  have hder : HasDerivAt (fun t : ℂ => u (p + t • v)) (fderiv ℂ u p v) 0 := by
    have h1 : HasFDerivAt u (fderiv ℂ u p) (p + (0 : ℂ) • v) := by
      simpa using hup.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hline 0)
  rw [← hder.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc
    (fun z hz => hM _ (hmem z (Metric.sphere_subset_closedBall hz)))

theorem norm_fderiv_le_of_bounded {n : ℕ} {p : ReciprocityTheory.L2DbarEstimates.V n} {ρ R M : ℝ}
    (hρ : (0 : ℝ) < ρ) (hR : ρ < R) (u : ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ :=
  norm_fderiv_le_of_bounded_gen hρ hR u hu hM

end GlobalTheory.FrechetDerivativeBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicValueDerivativeL2Ball

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem l2ball_sq_mul_vol_le {n : ℕ} {x : V n} {s : ℝ} (u : V n → ℂ)
    (hu : DifferentiableOn ℂ u (ball x s)) :
    ENNReal.ofReal (‖u x‖ ^ 2) * volume (ball (0 : V n) s) ≤
      ∫⁻ v in ball x s, ENNReal.ofReal (‖u v‖ ^ 2) := by
  have hu' : DifferentiableOn ℂ (fun y => u (x + y)) (ball 0 s) := by
    intro y hy
    have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    exact ((hu.differentiableAt (isOpen_ball.mem_nhds hxy)).comp y
      ((differentiable_const x).add differentiable_id y)).differentiableWithinAt
  have hρm : Measurable fun t : ℝ => (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) t :=
    measurable_const.indicator measurableSet_Iio
  have h := ReciprocityTheory.L2DbarEstimates.mv n s _ _ hu' hρm
    (fun t ht => Set.indicator_of_notMem (by simpa using ht) _)
  have e1 : ∀ y : V n, (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) ‖y‖ =
      (ball (0 : V n) s).indicator 1 y := by
    intro y
    by_cases hy : ‖y‖ < s
    · rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using hy)]; rfl
    · rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using hy)]
  simp only [add_zero, e1] at h
  rw [lintegral_indicator_one measurableSet_ball] at h
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self (fun v => (ball x s).indicator (fun v => ENNReal.ofReal (‖u v‖ ^ 2)) v) x]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ ball (0 : V n) s
  · have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hxy]; simp
  · have hxy : x + y ∉ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hxy]; simp

theorem norm_fderiv_le_of_ball {n : ℕ} {p : V n} {ρ R M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (u : V n → ℂ) (hu : DifferentiableOn ℂ u (ball p R)) (hM : ∀ x ∈ ball p R, ‖u x‖ ≤ M) :
    ‖fderiv ℂ u p‖ ≤ M / ρ := by
  first
  | exact @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | (apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded ..)

theorem l2_value_deriv_ball :
    ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ),
      DifferentiableOn ℂ u (ball p r) →
        ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
          ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  intro n r hr
  set β : ℝ := (volume (ball (0 : V n) (r / 2))).toReal with hβdef
  have hβ : 0 < β := ENNReal.toReal_pos (measure_ball_pos volume _ (by linarith)).ne'
    measure_ball_lt_top.ne
  have hV : volume (ball (0 : V n) (r / 2)) = ENNReal.ofReal β :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  refine ⟨(1 + 16 / r ^ 2) / β, by positivity, fun p u hu => ?_⟩
  set I := ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) with hIdef
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact le_top
  set J := I.toReal with hJ
  have hI' : I = ENNReal.ofReal J := (ENNReal.ofReal_toReal hI).symm
  have hx : ∀ x ∈ ball p (r / 2), ‖u x‖ ^ 2 ≤ J / β := by
    intro x hx
    have hsub : ball x (r / 2) ⊆ ball p r := by
      apply ball_subset_ball'
      rw [mem_ball] at hx; linarith
    have h2 := (l2ball_sq_mul_vol_le u (hu.mono hsub)).trans (lintegral_mono_set hsub)
    rw [hV, ← ENNReal.ofReal_mul (sq_nonneg _), ← hIdef, hI'] at h2
    rw [le_div_iff₀ hβ]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
  set M := Real.sqrt (J / β) with hMdef
  have hJβ : 0 ≤ J / β := div_nonneg ENNReal.toReal_nonneg hβ.le
  have hMx : ∀ x ∈ ball p (r / 2), ‖u x‖ ≤ M := by
    intro x hx'
    have := Real.sqrt_le_sqrt (hx x hx')
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hD := norm_fderiv_le_of_ball (ρ := r / 4) (by positivity) (by linarith) u
    (hu.mono (ball_subset_ball (by linarith))) hMx
  have hD2 : ‖fderiv ℂ u p‖ ^ 2 ≤ 16 / r ^ 2 * (J / β) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hD 2
    refine this.trans (le_of_eq ?_)
    rw [div_pow, Real.sq_sqrt hJβ]; field_simp; ring
  have hp := hx p (mem_ball_self (by linarith))
  rw [hI', ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ J / β + 16 / r ^ 2 * (J / β) := add_le_add hp hD2
    _ = (1 + 16 / r ^ 2) / β * J := by ring

end

end GlobalTheory
end
end
