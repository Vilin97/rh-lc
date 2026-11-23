module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfN
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfB
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtNull
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfD
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfF
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfC

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivC

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Set Filter

variable {n : ℕ}

theorem dense_nonzero {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {z : V n} (hz : z ∈ U) :
    ∃ᶠ y in 𝓝 z, y ∈ U ∧ g y ≠ 0 := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  have hz0 : ∀ᶠ y in 𝓝 z, g y = 0 := by
    filter_upwards [hcon, hU.mem_nhds hz] with y hy hyU
    by_contra h
    exact hy ⟨hyU, h⟩
  have hsub : U ⊆ {y | ∀ᶠ x in 𝓝 y, g x = 0} := by
    refine hUc.subset_of_closure_inter_subset isOpen_setOf_eventually_nhds ⟨z, hz, hz0⟩ ?_
    rintro y ⟨hycl, hyU⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y hyU
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hycl ε hε
    have hbb : b ∈ ball y ε := by
      rw [mem_ball, dist_comm]
      exact hdist
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball y ε) g b isOpen_ball (convex_ball y ε)
      (hg.mono hball) hbb hb
    exact Filter.eventually_of_mem (ball_mem_nhds y hε) (fun w hw => by simpa using hEq hw)
  obtain ⟨w, hwU, hw⟩ := hg0
  exact hw (hsub hwU).self_of_nhds

theorem ext_glue {U : Set (V n)} (hU : IsOpen U) (hUc : IsPreconnected U) {g : V n → ℂ}
    (hg : DifferentiableOn ℂ g U) (hg0 : ∃ z ∈ U, g z ≠ 0) {H : V n → ℂ}
    (hH : DifferentiableOn ℂ H (U ∩ {z | g z ≠ 0}))
    (hloc : ∀ z ∈ U, ∃ r > 0, ball z r ⊆ U ∧
      IntegrableOn (fun y => ‖H y‖ ^ 2) (ball z r \ {y | g y = 0})) :
    ∃ H' : V n → ℂ, DifferentiableOn ℂ H' U ∧ EqOn H' H (U ∩ {z | g z ≠ 0}) := by
  classical
  choose! r hr hrU hint using hloc

  have hE : ∀ z ∈ U, ∃ E : V n → ℂ, DifferentiableOn ℂ E (ball z (r z)) ∧
      EqOn E H (ball z (r z) \ {y | g y = 0}) := by
    intro z hz
    exact ReciprocityTheory.L2DbarEstimates.C.ext n (ball z (r z)) g H isOpen_ball (hg.mono (hrU z hz))
      (hH.mono (fun y hy => ⟨hrU z hz hy.1, hy.2⟩)) (hint z hz)
  choose! E hEd hEe using hE

  have hagree : ∀ y ∈ U, ∀ z ∈ U, ∀ w ∈ ball y (r y) ∩ ball z (r z), E y w = E z w := by
    intro y hy z hz w hw
    have hwU : w ∈ U := hrU y hy hw.1
    have hopen : IsOpen (ball y (r y) ∩ ball z (r z)) := isOpen_ball.inter isOpen_ball
    have hc1 : ContinuousAt (E y) w :=
      (hEd y hy).continuousOn.continuousAt (isOpen_ball.mem_nhds hw.1)
    have hc2 : ContinuousAt (E z) w :=
      (hEd z hz).continuousOn.continuousAt (isOpen_ball.mem_nhds hw.2)
    have hfreq : ∃ᶠ v in 𝓝 w, E y v - E z v ∈ ({0} : Set ℂ) := by
      have h1 := (dense_nonzero hU hUc hg hg0 hwU).and_eventually
        (hopen.mem_nhds hw : ∀ᶠ v in 𝓝 w, v ∈ ball y (r y) ∩ ball z (r z))
      refine h1.mono ?_
      rintro v ⟨⟨-, hgv⟩, hv1, hv2⟩
      rw [Set.mem_singleton_iff, sub_eq_zero, hEe y hy ⟨hv1, hgv⟩, hEe z hz ⟨hv2, hgv⟩]
    have h0 := isClosed_singleton.mem_of_frequently_of_tendsto hfreq (hc1.sub hc2)
    simpa [sub_eq_zero] using h0
  refine ⟨fun w => E w w, ?_, ?_⟩
  · intro z hz
    have hev : (fun w => E w w) =ᶠ[𝓝 z] E z := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (hr z hz)), hU.mem_nhds hz]
        with w hw hwU
      exact hagree w hwU z hz w ⟨mem_ball_self (hr w hwU), hw⟩
    exact (((hEd z hz).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self (hr z hz)))).congr_of_eventuallyEq hev).differentiableWithinAt
  · rintro w ⟨hwU, hgw⟩
    exact hEe w hwU ⟨mem_ball_self (hr w hwU), hgw⟩

end UpDivC

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPfE

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace UpDivE

open NumberField Complex Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates UpDivD
open scoped ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (Xa : ArchInM X) (x0 : Frame X.Ψ r) (bb : ℝ)

theorem w_hol (k : Fin Xa.N) : DifferentiableOn ℂ (fun z => Xa.w k (cpt X x0 z)) (OmF X x0) := by
  exact ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.hol_comp (X := X) (x0 := x0) (Xa.w_van k).1.1.1.1

theorem Sw_eq : Sw X Xa x0 = fun z => sqNorm fun k => Xa.w k (cpt X x0 z) := by
  funext z
  simp [Sw, sqNorm, Complex.sq_norm]

theorem logSw_cdAt {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (Sw X Xa x0 y)) z := by
  have hopen := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF (X := X) (x0 := x0)
  have hk : ∀ k, ContDiffAt ℝ ∞ (fun y => ‖Xa.w k (cpt X x0 y)‖ ^ 2) z := by
    intro k
    have hd := w_hol X Xa x0 k
    have h1 : ContDiffAt ℂ ∞ (fun y => Xa.w k (cpt X x0 y)) z :=
      ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct hopen hd hz
    exact (h1.restrict_scalars ℝ).norm_sq ℝ
  have hS : ContDiffAt ℝ ∞ (Sw X Xa x0) z := by
    have : Sw X Xa x0 = fun y => ∑ k, ‖Xa.w k (cpt X x0 y)‖ ^ 2 := rfl
    rw [this]
    exact ContDiffAt.sum fun k _ => hk k
  have hpos : 0 < Sw X Xa x0 z := by
    obtain ⟨k, hk0⟩ := Xa.w_nz _ hz
    exact Finset.sum_pos' (fun k _ => by positivity) ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hk0) 2⟩
  exact hS.log hpos.ne'

theorem plurisubharmonicWeight_smooth : ContDiffOn ℝ ∞ (ph0 X Xa x0 bb) (OmF X x0) := by
  intro z hz
  have h1 := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.phla_cpt_cdAt (X := X) x0 hz Xa.Fp
  have h2 := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.logDens_contDiffAt (X := X) (x0 := x0) hz
  have h3 := logSw_cdAt X Xa x0 hz
  have h4 := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.rhF_contDiffAt (X := X) (x0 := x0) hz
  have h := ((h1.sub h2).add ((contDiffAt_const (c := (1 / 2 : ℝ))).mul h3)).sub
    ((contDiffAt_const (c := bb)).mul h4)
  exact h.contDiffWithinAt

theorem levi_logSw_nonneg {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => ((Real.log (Sw X Xa x0 y) : ℝ) : ℂ)) z ξ).re := by
  have hopen := ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB.isOpen_OmF (X := X) (x0 := x0)
  simp only [Sw_eq X Xa x0]
  have hg : ∀ k, ContDiffAt ℂ 2 (fun y => Xa.w k (cpt X x0 y)) z := by
    intro k
    have hd := w_hol X Xa x0 k
    exact (ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct hopen hd hz).of_le (by norm_cast)
  have hne : (fun k => Xa.w k (cpt X x0 z)) ≠ 0 := by
    obtain ⟨k, hk0⟩ := Xa.w_nz _ hz
    intro h
    exact hk0 (congrFun h k)
  have hl := leviLogNormSq (nd X) Xa.N (fun k y => Xa.w k (cpt X x0 y)) z ξ hg hne
  beta_reduce at hl
  rw [hl, Complex.ofReal_re]
  have hnn : ∀ {p : ℕ} (v : Fin p → ℂ), 0 ≤ sqNorm v := fun v =>
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  exact div_nonneg (hnn _) (hnn _)

theorem leviForm_weight_nonneg {m : ℝ} (hbm : bb ≤ m) (ho : IsOrth X x0)
    (hmar : ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ)
    {z : V (nd X)} (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) z ξ).re := by
  have hA := (IW.phla_cpt_cdAt X x0 hz Xa.Fp).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hB := (OntoB.logDens_contDiffAt hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hC := (logSw_cdAt X Xa x0 hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  have hD := (OntoB.rhF_contDiffAt hz).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)
  set u : Fin 4 → V (nd X) → ℝ := ![fun w => phla X Xa.Fp (cpt X x0 w),
    fun w => -1 * Real.log (densF X x0 w) + 0, fun w => 1 / 2 * Real.log (Sw X Xa x0 w) + 0,
    fun w => -bb * rhF X x0 w + 0] with hu
  have hu0 : u 0 = fun w => phla X Xa.Fp (cpt X x0 w) := rfl
  have hu1 : u 1 = fun w => -1 * Real.log (densF X x0 w) + 0 := rfl
  have hu2 : u 2 = fun w => 1 / 2 * Real.log (Sw X Xa x0 w) + 0 := rfl
  have hu3 : u 3 = fun w => -bb * rhF X x0 w + 0 := rfl
  have hcu : ∀ i, ContDiffAt ℝ 2 (u i) z := by
    intro i; fin_cases i
    · show ContDiffAt ℝ 2 (u 0) z; rw [hu0]; exact hA
    · show ContDiffAt ℝ 2 (u 1) z; rw [hu1]; exact (contDiffAt_const.mul hB).add contDiffAt_const
    · show ContDiffAt ℝ 2 (u 2) z; rw [hu2]; exact (contDiffAt_const.mul hC).add contDiffAt_const
    · show ContDiffAt ℝ 2 (u 3) z; rw [hu3]; exact (contDiffAt_const.mul hD).add contDiffAt_const
  have he : (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) = fun w => ((∑ i, u i w : ℝ) : ℂ) := by
    funext w
    rw [Fin.sum_univ_four, hu0, hu1, hu2, hu3]
    unfold ph0
    push_cast; ring
  rw [he, leviV_ofReal_sum hcu, Complex.re_sum, Fin.sum_univ_four]
  have e1 := Y.leviV_const_mul (f := fun w => Real.log (densF X x0 w)) hB (-1) 0 ξ
  have e2 := Y.leviV_const_mul (f := fun w => Real.log (Sw X Xa x0 w)) hC (1 / 2) 0 ξ
  have e3 := Y.leviV_const_mul (f := fun w => rhF X x0 w) hD (-bb) 0 ξ
  rw [hu0, hu1, hu2, hu3, e1, e2, e3]
  have hm := hmar z hz ξ
  have hrh := ExF.levi_rhF_nonneg X x0 ho hz ξ
  have hlw := levi_logSw_nonneg X Xa x0 hz ξ
  unfold leviO leviM leviDens leviRh at hm
  simp only [Complex.re_ofReal_mul] at *
  have : (m - bb) * (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z ξ).re ≥ 0 :=
    mul_nonneg (by linarith) hrh
  nlinarith

end UpDivE

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.UpDivStatementPf

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField Complex Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates UpDivD
open scoped ENNReal ContDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace UpDivG

variable {r : ℕ}

theorem sum_bdd (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (P : Fin N → Frame X.Ψ r → ℂ)
    (hP : ∀ k, X.IsBddSec la (P k)) : ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨∑ k, C k ^ 2, fun x hx => Finset.sum_le_sum fun k _ => ?_⟩
  have h0 : 0 ≤ X.pnorm la (P k) x := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun τ _ =>
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact pow_le_pow_left₀ h0 (hC k x hx) 2

end UpDivG

theorem upDiv_holds : UpDivStatement (E := E) := by
  intro r X Xa Fl _ _ bb m _ hm hmar _ x0 ho F hF hIn
  classical
  have hU : IsOpen (OmF X x0) := OntoB.isOpen_OmF X x0
  have hUc : IsPreconnected (OmF X x0) := OFC.omFConn_of_cm r X x0 ho
  have hbm : bb ≤ m := by
    have : 0 ≤ bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) := by positivity
    linarith
  have hn2 : 2 ≤ nd X := Xa.n_ge
  have hTn : nd X ≤ Xa.T := by have := Xa.T_ge; nlinarith
  have hInU := hIn
  unfold InAt at hInU
  rw [IW.muF_lintegral] at hInU
  obtain ⟨Cs, hCs⟩ := UpDivG.sum_bdd X Xa.L Fl.s (fun k => (Fl.s_van k).1.1)
  obtain ⟨Cw, hCw⟩ := UpDivG.sum_bdd X Xa.L Xa.w (fun k => (Xa.w_van k).1.1)
  by_cases hex : ∃ k, ∃ z ∈ OmF X x0, Fl.s k (cpt X x0 z) ≠ 0
  swap
  ·
    simp only [not_exists, not_and, not_not] at hex
    have hWtop : ∀ z ∈ OmF X x0, WSk X Xa Fl (cpt X x0 z) = ⊤ := by
      intro z hz
      have hp : cpt X x0 z ∈ X.dom := hz
      have hs0 : ∑ k, X.pnorm Xa.L (Fl.s k) (cpt X x0 z) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [pnorm_sq X hp, hex k z hz, norm_zero]; ring
      have hwp : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2 := by
        rw [sumL_eq X Xa x0 hz]; exact mul_pos (Real.exp_pos _) (Sw_pos X Xa x0 hz)
      unfold WSk
      rw [if_pos hp, hs0, zero_div, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by
        have : (1 : ℝ) ≤ Xa.T := by exact_mod_cast (show 1 ≤ Xa.T by omega)
        linarith)]
      refine ENNReal.mul_top ?_
      exact mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
        (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hwp) ENNReal.ofReal_ne_top).ne'
    have hF0 : ∀ z ∈ OmF X x0, F z = 0 := by
      intro z0 hz0
      by_contra hne
      have hev1 : ∀ᶠ y in 𝓝 z0, y ∈ OmF X x0 := hU.mem_nhds hz0
      have hev : ∀ᶠ y in 𝓝 z0, y ∈ OmF X x0 ∧ F y ≠ 0 :=
        hev1.and ((hF.continuousOn.continuousAt (hU.mem_nhds hz0)).eventually_ne hne)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
      have hsub : Metric.ball z0 ε ⊆ OmF X x0 := fun y hy => (hball y hy).1
      have htop : ∫⁻ y in Metric.ball z0 ε, ENNReal.ofReal (densF X x0 y) *
          (ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) * WSk X Xa Fl (cpt X x0 y)) = ⊤ := by
        rw [setLIntegral_congr_fun measurableSet_ball (g := fun _ => ⊤) fun y hy => ?_,
          setLIntegral_const, ENNReal.top_mul (Metric.measure_ball_pos volume z0 hε).ne']
        have hyO := hsub hy
        have ha : ENNReal.ofReal (densF X x0 y) ≠ 0 := (ENNReal.ofReal_pos.mpr (OntoB.densF_pos hyO)).ne'
        have hb : ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) ≠ 0 := by
          refine (ENNReal.ofReal_pos.mpr (div_pos ?_ (Real.exp_pos _))).ne'
          have := (hball y hy).2; positivity
        rw [hWtop y hyO, ENNReal.mul_top hb, ENNReal.mul_top ha]
      have := lt_of_le_of_lt (lintegral_mono_set hsub) hInU
      rw [htop] at this
      exact lt_irrefl _ this
    refine ⟨fun _ _ => 0, fun α _ => ⟨differentiableOn_const _, ?_⟩, fun z hz => ?_⟩
    · unfold InAt; simp
    · rw [hF0 z hz]; simp

  obtain ⟨k1, z1, hz1, hk1⟩ := hex
  set g1 : V (nd X) → ℂ := fun z => Fl.s k1 (cpt X x0 z) with hg1def
  have hg1 : DifferentiableOn ℂ g1 (OmF X x0) := OntoB.hol_comp X x0 (Fl.s_van k1).1.1.1.1
  have hg10 : ∃ z ∈ OmF X x0, g1 z ≠ 0 := ⟨z1, hz1, hk1⟩
  set U' : Set (V (nd X)) := {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} with hU'def
  have hU'o : IsOpen U' := ExG.isOpen_Om X x0 g1 hg1
  obtain ⟨S, hSz, -⟩ := exhaustG_holds r X x0 ho g1 hg1
  set sv : Fin (nd X) → V (nd X) → ℂ := fun k z => Fl.s k (cpt X x0 z) with hsv
  have hsvO : ∀ k, DifferentiableOn ℂ (sv k) (OmF X x0) := fun k =>
    OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1
  have hsvd : ∀ k, DifferentiableOn ℂ (sv k) U' := fun k => (hsvO k).mono fun z hz => hz.1
  have hnz : ∀ y ∈ U', ∃ i, sv i y ≠ 0 := fun y hy => ⟨k1, hy.2⟩
  have hph : ContDiffOn ℝ ∞ (ph0 X Xa x0 bb) U' :=
    (UpDivE.plurisubharmonicWeight_smooth X Xa x0 bb).mono fun z hz => hz.1
  have hl : ∀ y ∈ U', ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((ph0 X Xa x0 bb w : ℝ) : ℂ)) y ξ).re :=
    fun y hy ξ => UpDivE.leviForm_weight_nonneg X Xa x0 bb hbm ho (hmar x0 ho) hy.1 ξ
  have hSs : ∀ y ∈ U', 0 < Ss X Xa Fl x0 y := fun y hy =>
    Finset.sum_pos' (fun _ _ => by positivity) ⟨k1, Finset.mem_univ _, by have := hy.2; positivity⟩
  have hI : ∫⁻ y in U', ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖sv i y‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2)) *
      Real.exp (-ph0 X Xa x0 bb y)) < ⊤ := by
    refine lt_of_le_of_lt ?_ hInU
    calc ∫⁻ y in U', ENNReal.ofReal (‖F y‖ ^ 2 * (∑ i, ‖sv i y‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2)) *
          Real.exp (-ph0 X Xa x0 bb y))
        = ∫⁻ y in U', ENNReal.ofReal (densF X x0 y) *
            (ENNReal.ofReal (‖F y‖ ^ 2 / kaF X x0 bb y) * WSk X Xa Fl (cpt X x0 y)) := by
          refine setLIntegral_congr_fun hU'o.measurableSet fun y hy => ?_
          exact (wSk_eq X Xa Fl x0 bb hy.1 (hSs y hy) F).symm
      _ ≤ _ := lintegral_mono_set fun y hy => hy.1
  have hcond : ((nd X : ℕ) : ℝ) - 1 < (Xa.T : ℝ) - 1 / 2 - ((Xa.T - nd X : ℕ) : ℝ) - 1 + 1 := by
    rw [Nat.cast_sub hTn]; linarith
  obtain ⟨H, hH, hid⟩ := UpDivB.iter_div hU'o S hSz sv (ph0 X Xa x0 bb) hn2 hsvd hnz hph hl
    ((Xa.T : ℝ) - 1 / 2) (Xa.T - nd X) hcond F (hF.mono fun z hz => hz.1) hI
  have hexp : ((Xa.T : ℝ) - 1 / 2 - ((Xa.T - nd X : ℕ) : ℝ)) = (nd X : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub hTn]; ring
  have hSc : ContinuousOn (Ss X Xa Fl x0) (OmF X x0) :=
    continuousOn_finsetSum _ fun k _ => ((hsvO k).continuousOn.norm).pow 2
  have hpc : ContinuousOn (ph0 X Xa x0 bb) (OmF X x0) := (UpDivE.plurisubharmonicWeight_smooth X Xa x0 bb).continuousOn
  have hω : ∀ K ⊆ OmF X x0, IsCompact K → ∃ c > 0, ∀ y ∈ K ∩ U',
      c ≤ (∑ i, ‖sv i y‖ ^ 2) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-ph0 X Xa x0 bb y) := by
    intro K hKU hK
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hSc.mono hKU)
    obtain ⟨P, hP⟩ := hK.exists_bound_of_continuousOn (hpc.mono hKU)
    refine ⟨(max M 1) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-P), by positivity, fun y hy => ?_⟩
    have hsy := hSs y hy.2
    have hle : Ss X Xa Fl x0 y ≤ max M 1 := by
      have := hM y hy.1
      rw [Real.norm_of_nonneg hsy.le] at this
      exact this.trans (le_max_left _ _)
    have ha : (0 : ℝ) ≤ (nd X : ℝ) - 1 / 2 := by
      have : (2 : ℝ) ≤ nd X := by exact_mod_cast hn2
      linarith
    have h1 : (max M 1) ^ (-((nd X : ℝ) - 1 / 2)) ≤ (Ss X Xa Fl x0 y) ^ (-((nd X : ℝ) - 1 / 2)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_neg hsy.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hsy _) (Real.rpow_le_rpow hsy.le hle ha)
    have h2 : Real.exp (-P) ≤ Real.exp (-ph0 X Xa x0 bb y) := by
      refine Real.exp_le_exp.mpr ?_
      have := hP y hy.1
      have := le_abs_self (ph0 X Xa x0 bb y)
      rw [Real.norm_eq_abs] at *
      linarith
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.rpow_nonneg hsy.le _)
  have hext : ∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), ∃ H' : V (nd X) → ℂ,
      DifferentiableOn ℂ H' (OmF X x0) ∧ EqOn H' (H α) U' := by
    intro α hα
    have hIα : ∫⁻ y in U', ENNReal.ofReal (‖H α y‖ ^ 2 *
        ((∑ i, ‖sv i y‖ ^ 2) ^ (-((nd X : ℝ) - 1 / 2)) * Real.exp (-ph0 X Xa x0 bb y))) < ⊤ := by
      have := (hH α hα).2
      rw [hexp] at this
      simpa only [mul_assoc] using this
    have hloc := UpDivF.loc_int hU hU'o (g := g1) (fun y => Iff.rfl) (hH α hα).1.continuousOn hω hIα
    exact UpDivC.ext_glue hU hUc hg1 hg10 (hH α hα).1 hloc
  choose! Hx hHxd hHxeq using hext
  refine ⟨Hx, fun α hα => ⟨hHxd α hα, ?_⟩, fun z hz => ?_⟩
  · unfold InAt
    rw [IW.muF_lintegral]
    have hnull := UpDivF.zero_null hU hUc hg1 hg10
    have hae : (OmF X x0 : Set (V (nd X))) =ᵐ[volume] U' := by
      refine ae_eq_set.mpr ⟨?_, ?_⟩
      · refine measure_mono_null (fun y hy => ?_) hnull
        refine ⟨hy.1, ?_⟩
        by_contra h
        exact hy.2 ⟨hy.1, h⟩
      · have : U' \ OmF X x0 = ∅ := by
          ext y; simp only [Set.mem_sdiff, mem_empty_iff_false, iff_false]
          exact fun h => h.2 h.1.1
        rw [this, measure_empty]
    rw [setLIntegral_congr hae]
    have hn12 : (1 / 2 : ℝ) ≤ (nd X : ℝ) := by
      have : (2 : ℝ) ≤ nd X := by exact_mod_cast hn2
      linarith
    calc ∫⁻ y in U', ENNReal.ofReal (densF X x0 y) *
          (ENNReal.ofReal (‖Hx α y‖ ^ 2 / kaF X x0 bb y) * weightFunctionOnFrames X Xa (cpt X x0 y))
        ≤ ∫⁻ y in U', ENNReal.ofReal (Cs ^ ((nd X : ℝ) - 1 / 2) * Cw ^ (1 / 2 : ℝ)) *
            ENNReal.ofReal (‖H α y‖ ^ 2 * Ss X Xa Fl x0 y ^ (-((nd X : ℝ) - 1 / 2)) *
              Real.exp (-ph0 X Xa x0 bb y)) := by
          refine setLIntegral_mono' hU'o.measurableSet fun y hy => ?_
          rw [hHxeq α hα hy]
          exact weightedDensity_bound X Xa Fl x0 bb hy.1 (hSs y hy) (H α) (hCs _ hy.1) (hCw _ hy.1) hn12
      _ < ⊤ := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
          have := (hH α hα).2
          rw [hexp] at this
          exact this
  · have hcont : ContinuousOn (fun z => F z - ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
        (∏ k, Fl.s k (cpt X x0 z) ^ α k) * Hx α z) (OmF X x0) := by
      refine hF.continuousOn.sub (continuousOn_finsetSum _ fun α hα => ?_)
      exact (continuousOn_finsetProd _ fun k _ => ((hsvO k).continuousOn.pow _)).mul
        (hHxd α hα).continuousOn
    have h0 := UpDivF.eq_across hU hUc hg1 hg10 hcont (fun y hy hgy => by
      have hy' : y ∈ U' := ⟨hy, hgy⟩
      rw [hid y hy', sub_eq_zero]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [hHxeq α hα hy']) z hz
    exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
end
