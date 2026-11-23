module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Topology.Separation.CompletelyRegular

-- Source module: Lemmata.MiscLemmasF.Imports

section

@[expose] public section

namespace Bl.SecondBlockLemmaG

theorem goal1 :
  ∀ {n : Nat} {Ω K : Set.{0} (ReciprocityTheory.L2DbarEstimates.C.V n)} {u : ReciprocityTheory.L2DbarEstimates.C.V n → Complex},
  IsOpen.{0} Ω →
    DifferentiableOn.{0, 0, 0} Complex u Ω →
      IsCompact.{0} K →
        LE.le.{0} K Ω →
          ∀ (v : ReciprocityTheory.L2DbarEstimates.C.V n),
            Exists.{1} fun (C : Real) ↦
              ∀ (x : ReciprocityTheory.L2DbarEstimates.C.V n),
                Membership.mem.{0, 0} K x →
                  LE.le.{0} (Norm.norm.{0} (DFunLike.coe.{1, 1, 1} (fderiv.{0, 0, 0} Real u x) v)) C := by
  intro n Ω K u hΩ hu hK hKΩ v
  obtain ⟨δ, hδ, hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨M, hM⟩ := (hK.cthickening (r := δ)).exists_bound_of_continuousOn
    (hu.continuousOn.mono hδΩ)
  by_cases hv : v = 0
  · refine ⟨0, fun x _ => ?_⟩
    simp [hv]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    refine ⟨M / (δ / ‖v‖), fun x hx => ?_⟩
    have hr : 0 < δ / ‖v‖ := div_pos hδ hvpos
    have hux : DifferentiableAt ℂ u x :=
      (hu x (hKΩ hx)).differentiableAt (hΩ.mem_nhds (hKΩ hx))
    have hR : fderiv ℝ u x v = fderiv ℂ u x v := by
      rw [(hux.hasFDerivAt.restrictScalars ℝ).fderiv]
      rfl
    have hmem : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) (δ / ‖v‖) →
        x + z • v ∈ Metric.cthickening δ K := by
      intro z hz
      apply Metric.closedBall_subset_cthickening hx
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      calc ‖z‖ * ‖v‖ ≤ δ / ‖v‖ * ‖v‖ := by gcongr
        _ = δ := div_mul_cancel₀ δ hvpos.ne'
    have hgd : DifferentiableOn ℂ (fun z : ℂ => u (x + z • v))
        (Metric.closedBall (0 : ℂ) (δ / ‖v‖)) := by
      intro z hz
      have h1 : DifferentiableAt ℂ u (x + z • v) :=
        (hu _ (hδΩ (hmem z hz))).differentiableAt (hΩ.mem_nhds (hδΩ (hmem z hz)))
      have h2 : DifferentiableAt ℂ (fun w : ℂ => x + w • v) z :=
        (differentiableAt_id.smul_const v).const_add x
      exact (h1.comp z h2).differentiableWithinAt
    have hdc := hgd.diffContOnCl_ball subset_rfl
    have hest := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdc
      (fun z hz => hM _ (hmem z (Metric.sphere_subset_closedBall hz)))
    have hderiv : HasDerivAt (fun z : ℂ => u (x + z • v)) (fderiv ℂ u x v) 0 := by
      have h2 : HasDerivAt (fun w : ℂ => x + w • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
      have h1 : HasFDerivAt u (fderiv ℂ u x) (x + (0 : ℂ) • v) := by
        simpa using hux.hasFDerivAt
      exact h1.comp_hasDerivAt 0 h2
    rw [hR, ← hderiv.deriv]
    exact hest

end Bl.SecondBlockLemmaG
end
end

-- Source module: ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeak

section

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem holoWeak_bound {n : ℕ} {Ω K : Set (V n)} {u : V n → ℂ} (hΩ : IsOpen Ω)
    (hu : DifferentiableOn ℂ u Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (v : V n) :
    ∃ C : ℝ, ∀ x ∈ K, ‖fderiv ℝ u x v‖ ≤ C := by
  first | exact Bl.SecondBlockLemmaG.goal1 .. | (apply Bl.SecondBlockLemmaG.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaG.goal1 <;> assumption)

theorem holoWeak : HoloWeakStatement := by
  intro n Ω u hΩ hu
  refine ⟨hu.continuousOn.locallyIntegrableOn hΩ.measurableSet, ?_⟩
  intro g hg v
  obtain ⟨hgs, hgc, hgΩ⟩ := hg
  have hK : IsCompact (tsupport g) := hgc
  have huK : ContinuousOn u (tsupport g) := hu.continuousOn.mono hgΩ
  have hg1 : ContDiff ℝ 1 g := hgs.of_le (by exact_mod_cast le_top)
  have hgd : Differentiable ℝ g := hg1.differentiable one_ne_zero
  have hg'c : ∀ w : V n, Continuous fun x => fderiv ℝ g x w := fun w =>
    (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hzero : ∀ x, x ∉ tsupport g → g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hzero' : ∀ w x, x ∉ tsupport g → fderiv ℝ g x w = 0 := fun w x hx => by
    rw [fderiv_of_notMem_tsupport ℝ hx]; rfl
  have hint : ∀ h : V n → ℂ, Continuous h → (∀ x, x ∉ tsupport g → h x = 0) →
      Integrable (fun x => u x * h x) := by
    intro h hh hh0
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := tsupport g) ?_ ?_
    · exact (huK.mul hh.continuousOn).integrableOn_compact hK
    · intro x hx; simp [hh0 x hx]
  have hgi : Integrable g := hgs.continuous.integrable_of_hasCompactSupport hgc
  have hibp : ∀ w : V n, ∫ x, u x * fderiv ℝ g x w = - ∫ x, fderiv ℝ u x w * g x := by
    intro w
    obtain ⟨C, hC⟩ := holoWeak_bound hΩ hu hK hgΩ w
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · refine Integrable.mono' (hgi.norm.const_mul C) ?_ (Eventually.of_forall fun x => ?_)
      · exact (measurable_fderiv_apply_const ℝ u w).aestronglyMeasurable.mul
          hgs.continuous.aestronglyMeasurable
      · by_cases hx : x ∈ tsupport g
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)
        · simp [hzero x hx]
    · exact hint _ (hg'c w) (hzero' w)
    · exact hint _ hgs.continuous hzero
    · intro x hx
      exact ((hu x (hgΩ hx)).differentiableAt (hΩ.mem_nhds (hgΩ hx))).restrictScalars ℝ
    · intro x _
      exact hgd x
  have hlin : ∀ x, fderiv ℝ u x (I • v) * g x = I * (fderiv ℝ u x v * g x) := by
    intro x
    by_cases hx : x ∈ tsupport g
    · have hux : DifferentiableAt ℂ u x :=
        (hu x (hgΩ hx)).differentiableAt (hΩ.mem_nhds (hgΩ hx))
      rw [hux.fderiv_restrictScalars (𝕜 := ℝ)]
      simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
      ring
    · simp [hzero x hx]
  have hΩ0 : ∀ x, x ∉ Ω → u x * dbarDir g x v = 0 := by
    intro x hx
    have hx' : x ∉ tsupport g := fun h => hx (hgΩ h)
    simp [dbarDir, fderiv_of_notMem_tsupport ℝ hx']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hΩ0]
  have e1 : (fun x => u x * dbarDir g x v) =
      fun x => u x * fderiv ℝ g x (I • v) - I * (u x * fderiv ℝ g x v) := by
    funext x; simp only [dbarDir]; ring
  rw [e1, integral_sub (hint _ (hg'c _) (hzero' _)) ((hint _ (hg'c _) (hzero' _)).const_mul I),
    integral_const_mul, hibp (I • v), hibp v]
  simp only [hlin]
  rw [integral_const_mul]
  ring

end ReciprocityTheory.L2DbarEstimates.C
end
end
