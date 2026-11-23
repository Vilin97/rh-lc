module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.OneDivisionUpstairsFreeWeightStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SingularMetricFreeDivisorInvariantLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SquareIntegrableSingularMetricOrderOneStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinSumMul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UnfoldPoincareOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SingularMetricFreeDivisorInvariantLowerBoundStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.singularMetricFreeDivisor_invariant_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → IsMetricW X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ WLower X (G + n • Xa.L) (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) ∧ ∀ x ∈ X.dom, (∃ k, Fl.s k x ≠ 0) → (fun x => open Classical in if x ∈ X.dom then ENNReal.ofReal (Real.exp (-phla X G x)) * ENNReal.ofReal (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ)) * ENNReal.ofReal (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2)) else 0) x = ENNReal.ofReal (Real.exp (-(fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) x)) := by
  first | exact @GlobalTheory.FreeDivMetric.freeDivMetric | exact GlobalTheory.FreeDivMetric.freeDivMetric | (intros; apply GlobalTheory.FreeDivMetric.freeDivMetric <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtCompCpt

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up

namespace DivLeviPf

section Euclid

variable {n p : ℕ} {g : Fin p → V n → ℂ} {y : V n}

theorem logSum_contDiffAt (hg : ∀ k, ContDiffAt ℂ ∞ (g k) y) (hne : ∃ k, g k y ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (∑ k, ‖g k w‖ ^ 2)) y := by
  have h1 : ContDiffAt ℝ ∞ (fun w => ∑ k, ‖g k w‖ ^ 2) y := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (hg k)
  exact h1.log (sum_normSq_pos hne).ne'

theorem logSum_levi_nonneg (hg : ∀ k, ContDiffAt ℂ ∞ (g k) y) (hne : ∃ k, g k y ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun w => ((Real.log (∑ k, ‖g k w‖ ^ 2) : ℝ) : ℂ)) y ξ).re := by
  obtain ⟨k0, hk0⟩ := hne
  have h := leviLogNormSq n p g y ξ (fun k => (hg k).of_le HE.two_le_inf)
    (fun h => hk0 (congrFun h k0))
  have e : (fun w => ((Real.log (∑ k, ‖g k w‖ ^ 2) : ℝ) : ℂ)) =
      fun w => ((Real.log (sqNorm (fun i => g i w)) : ℝ) : ℂ) := by
    funext w
    simp only [← Complex.normSq_eq_norm_sq]
    rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

end Euclid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem contDiffAt_comp_cpt {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom)
    (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℂ ∞ (fun w => P (cpt X x0 w)) z := by
  have hc : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)
  exact HE.contDiffAt_of_punct (ExF.isOpen_OmF X x0)
    (hP.comp hc.differentiableOn fun w hw => hw) hz

theorem exists_s_ne_zero {Xa : ArchInM X} (Fl : FlatM X Xa) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) :
    ∃ k, ∃ x ∈ X.dom, Fl.s k x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨j, -⟩ := (Fl.S_eq x0 hx0).1 fun k => h k x0 hx0
  have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
    show cpt X (Fl.xs j) 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact Fl.xs_mem j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(ExF.isOpen_OmF X (Fl.xs j)).mem_nhds h0] with w hw
    ext k
    simp [h k _ hw]
  apply Fl.coord j
  rw [hev.fderiv_eq, fderiv_fun_const]
  have h2 := Xa.n_ge
  have : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  show LinearMap.det (0 : V (nd X) →ₗ[ℂ] V (nd X)) = 0
  exact LinearMap.det_zero' (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis

end DivLeviPf


end GlobalTheory.Up
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SingularMetricFreeDivisorSmoothCurvature

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares


open GlobalTheory.Up.DivLeviPf in
theorem divLevi_freeWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → ∀ x0, IsOrth X x0 → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) ∧ ∀ k0 : Fin (nd X), ContDiffOn ℝ ∞ (fun z => (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0} ∧ ∀ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0 → ∀ ξ : Fin (nd X) → ℂ, leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ ≤ (leviV (nd X) (fun w => (((fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  intro E _ _ _ r X Xa Fl G n hn x0 ho
  have hsS : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hwS : ∀ k, X.IsSec Xa.L (Xa.w k) := fun k => (Xa.w_van k).1.1.1
  have hs : ∀ z ∈ OmF X x0, ∀ k, ContDiffAt ℂ ∞ (fun w => Fl.s k (cpt X x0 w)) z :=
    fun z hz k => contDiffAt_comp_cpt (hsS k).1 x0 hz
  have hw : ∀ z ∈ OmF X x0, ∀ k, ContDiffAt ℂ ∞ (fun w => Xa.w k (cpt X x0 w)) z :=
    fun z hz k => contDiffAt_comp_cpt (hwS k).1 x0 hz
  refine ⟨?_, fun k0 => ⟨fun z hz => ?_, fun z hz hz0 ξ => ?_⟩⟩
  · obtain ⟨k, x, hx, hne⟩ := exists_s_ne_zero Fl (IW.orth_mem_dom X x0 ho)
    by_contra h
    push Not at h
    exact hne (bigCellStatement_holds r X x0 ho Xa.L (Fl.s k) ⟨(hsS k).1, (hsS k).2.1⟩ (h k) x hx)
  · have h1 := IW.phla_cpt_cdAt X x0 hz.1 G
    have h2 := logSum_contDiffAt (hw z hz.1) (Xa.w_nz _ hz.1)
    have h3 := logSum_contDiffAt (hs z hz.1) ⟨k0, hz.2⟩
    exact ((h1.add (contDiffAt_const.mul h2)).add (contDiffAt_const.mul h3)).contDiffWithinAt
  · have h1 := (IW.phla_cpt_cdAt X x0 hz G).of_le HE.two_le_inf
    have h2 := (logSum_contDiffAt (hw z hz) (Xa.w_nz _ hz)).of_le HE.two_le_inf
    have h3 := (logSum_contDiffAt (hs z hz) ⟨k0, hz0⟩).of_le HE.two_le_inf
    have h4 := (IW.logDens_cdAt X x0 hz).of_le HE.two_le_inf
    have l2 := logSum_levi_nonneg (hw z hz) (Xa.w_nz _ hz) ξ
    have l3 := logSum_levi_nonneg (hs z hz) ⟨k0, hz0⟩ ξ
    have e : (fun w => (((fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
          ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 w) -
            Real.log (densF X x0 w) : ℝ) : ℂ)) =
        fun w => (((phla X G (cpt X x0 w) + (-1) * Real.log (densF X x0 w)) +
          ((1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 w)‖ ^ 2) +
            ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k (cpt X x0 w)‖ ^ 2)) : ℝ) : ℂ) := by
      funext w
      congr 1
      ring
    rw [e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (h1.add (contDiffAt_const.mul h4))
        ((contDiffAt_const.mul h2).add (contDiffAt_const.mul h3)),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h4),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2) (contDiffAt_const.mul h3),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2,
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    have hn' : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have l3' := mul_nonneg hn' l3
    unfold leviO leviM leviDens
    linarith

end GlobalTheory.Shares
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SingularMetricFreeDivisorSmoothCurvatureStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.singularMetricFreeDivisor_smooth_curvature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → ∀ x0, IsOrth X x0 → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) ∧ ∀ k0 : Fin (nd X), ContDiffOn ℝ ∞ (fun z => (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0} ∧ ∀ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0 → ∀ ξ : Fin (nd X) → ℂ, leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ ≤ (leviV (nd X) (fun w => (((fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  first | exact @GlobalTheory.Shares.divLevi_freeWeight | exact GlobalTheory.Shares.divLevi_freeWeight | (intros; apply GlobalTheory.Shares.divLevi_freeWeight <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DivisionOrderOne

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.DivFreeWeight

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra GlobalTheory.Up.DivCorePf

theorem division_order_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r), (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, m * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ) → (∀ P, X.IsBddSec (G + (nd X + 1) • Xa.L) P → P ∈ X.SS (G + (nd X + 1) • Xa.L)) → (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (G + (nd X + 1) • Xa.L), ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) → ∀ f, X.IsBddSec (G + (nd X + 1) • Xa.L) f → (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + (nd X + 1) • Xa.L) f x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (nd X + 1)) → (∀ j, f (Fl.xs j) = 0) → ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ k, X.IsBddSec (G + nd X • Xa.L) (h k)) ∧ ∀ x ∈ X.dom, f x = ∑ k, Fl.s k x * h k x := by
  intro E _ _ _ r X Xa Fl G ⟨bb, m, hbb, hbm, hmar⟩ hcusp ⟨K, gs, hgs⟩ f hf hfC hvan
  have h2 := Xa.n_ge
  have hPD : PropDisc X := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  obtain ⟨-, -, -, hPo, hOn⟩ := GlobalTheory.PoincareClosed.unfold_poincare_onto (E := E)
  have hExt := GlobalTheory.FrameMeasureClosed.extF_holds (E := E)
  obtain ⟨x0, ho⟩ : ∃ x0, IsOrth X x0 := by
    choose P hP hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ⟩
  obtain ⟨FF, hFF⟩ := fundSet_holds r X x0 ho hPD
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  have hbm' : bb ≤ m := by
    have : 0 ≤ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := by positivity
    linarith
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hIn := GlobalTheory.T.square_integrable_singular_metric_order_one E r X Xa Fl G x0 ho FF hFF f hf.1 hfC hvan
  obtain ⟨hMT, hLT, hET⟩ := GlobalTheory.T.singularMetricFreeDivisor_invariant_lower_bound E r X Xa Fl G (nd X + 1) (by omega)
  obtain ⟨hMn, hLn, -⟩ := GlobalTheory.T.singularMetricFreeDivisor_invariant_lower_bound E r X Xa Fl G (nd X) (by omega)
  obtain ⟨⟨k0, z0, hz0, hz0'⟩, hLev⟩ := GlobalTheory.T.singularMetricFreeDivisor_smooth_curvature E r X Xa Fl G (nd X + 1) (by omega) x0 ho
  obtain ⟨F, P, hF, hFI, hP, hPF, hpo⟩ := hOn r X x0 ho hPD _ _
    (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
      (((nd X + 1 : ℕ) : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2))
    (fun z => Fl.s k0 (cpt X x0 z)) bb m hMT hLT hbb hbm (OntoB.hol_comp X x0 (hs k0).1)
    ⟨z0, hz0, hz0'⟩ (hLev k0).1 (fun z hz hz' => hET _ hz ⟨k0, hz'⟩)
    (fun z hz hz' ξ => (hmar x0 ho z hz ξ).trans ((hLev k0).2 z hz hz' ξ)) hcusp FF hFF
    ⟨K, gs, fun f hf _ => hgs f hf⟩ _ (hcusp _ hf) hIn
  obtain ⟨H, hH, hFH⟩ := GlobalTheory.T.one_division_upstairs_free_weight E r X Xa Fl G x0 ho bb
    (fun z hz ξ => (mul_le_mul_of_nonneg_right hbm'
      (OntoB.levi_rh_nonneg RhGradFStatement_holds ho hz ξ)).trans (hmar x0 ho z hz ξ))
    ⟨k0, z0, hz0, hz0'⟩ F hF hFI
  choose Q hQ hQH using fun k => exists_extension hExt ho hLn hbb0 (hH k).1 (hH k).2
  have hPQ := fun k => hPo r X x0 ho hPD _ _ bb hMn hLn hbb (H k) (Q k) (hH k).1 (hH k).2 (hQ k) (hQH k)
  have hwt : G + (nd X + 1) • Xa.L = G + nd X • Xa.L + Xa.L := by
    rw [succ_nsmul, add_assoc]
  have hsum : ∀ y ∈ X.dom, P y = ∑ k, Fl.s k y * Q k y := by
    intro y hy
    refine sub_eq_zero.1 (bigCellStatement_holds r X x0 ho (G + (nd X + 1) • Xa.L)
      (fun y => P y - ∑ k, Fl.s k y * Q k y) ⟨?_, fun x hx b hb => ?_⟩ (fun z hz => ?_) y hy)
    · exact hP.1.sub (DifferentiableOn.fun_sum fun k _ => (hs k).1.mul (hQ k).1)
    · beta_reduce
      rw [mul_sub, hP.2 x hx b hb, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(hs k).2.1 x hx b hb, (hQ k).2 x hx b hb, hwt, bchar_add X hb _ Xa.L]
      ring
    · rw [hPF z hz, hFH z hz, sub_eq_zero]
      exact Finset.sum_congr rfl fun k _ => by rw [hQH k z hz]
  refine ⟨fun k => poin X (G + nd X • Xa.L) (Q k), fun k => (hPQ k).2.1, fun x hx => ?_⟩
  rw [← hpo x hx, hwt]
  exact poin_sum_mul _ (fun k _ => hs k) hsum hx fun k _ => (hPQ k).1 x hx

end GlobalTheory.DivFreeWeight
end
end
