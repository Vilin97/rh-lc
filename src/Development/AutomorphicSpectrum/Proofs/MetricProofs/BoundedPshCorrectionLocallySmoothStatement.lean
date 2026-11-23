module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralAngMeas
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DenseCoordinateTorusStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviFlatSeparatelyHarmonicStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChartStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonicStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmooth
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Linter.Style
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChartStatement
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmoothStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

theorem _root_.GlobalTheory.T.polydisc_poisson_smooth : ∀ (n : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℝ), 0 < ρ → Continuous (fun θ : Fin n → ℝ => h (torusPt ρ θ)) → ContDiffOn ℝ ∞ (polyPoisson ρ h) (Metric.ball 0 ρ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChart

section

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem contDiffAt_comp_compatChart_symm :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
      (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ),
      IsCompatChart A ψ → IsOpen U → A.SmoothOn U g →
        ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  intro e X _ A ψ U g hψ hU hg z hz hzU
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hτ : ContDiffAt ℝ ∞ (⇑(A.chart j) ∘ ⇑ψ.symm) z :=
    (((hψ j).2 z ⟨hz, hj⟩).contDiffAt).restrict_scalars ℝ
  have hy : (A.chart j) (ψ.symm z) ∈ (A.chart j).target ∩ ⇑(A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) (ψ.symm z)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact hzU
  have hgc : ContDiffAt ℝ ∞ (g ∘ ⇑(A.chart j).symm) ((A.chart j) (ψ.symm z)) :=
    (hg j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hcomp := hgc.comp z hτ
  apply hcomp.congr_of_eventuallyEq
  have hev : ∀ᶠ w in 𝓝 z, ψ.symm w ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart j).left_inv hw]

end GlobalTheory.CompanionTheory.Metric
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChartStatement

section

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.smooth_in_compatible_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ → IsOpen U → A.SmoothOn U g → ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  first | exact @GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | exact GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | (intros; apply GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartComposition

section

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem smoothOn_comp_compatChart (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ)
    (hψ : IsCompatChart A ψ) (hO : IsOpen O) (_hOt : O ⊆ ψ.target)
    (hG : ContDiffOn ℝ ∞ G O) : A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  intro j y hy
  obtain ⟨hyt, hys, hyO⟩ := hy
  have han : AnalyticAt ℂ (ψ ∘ (A.chart j).symm) y := (hψ j).1 y ⟨hyt, hys⟩
  have hτ : ContDiffAt ℝ ∞ (ψ ∘ (A.chart j).symm) y :=
    (han.restrictScalars (𝕜 := ℝ)).contDiffAt.of_le le_top
  have hGat : ContDiffAt ℝ ∞ G ((ψ ∘ (A.chart j).symm) y) :=
    hG.contDiffAt (hO.mem_nhds hyO)
  exact (hGat.comp y hτ).contDiffWithinAt

theorem smoothOn_comp_compatChart' : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) :=
  fun e X _ A ψ O G h1 h2 h3 h4 => smoothOn_comp_compatChart e X A ψ O G h1 h2 h3 h4

end GlobalTheory.CompanionTheory.Metric
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartCompositionStatement

section

@[expose] public section

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

theorem _root_.GlobalTheory.T.smoothOn_of_chart_composition : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (G : (Fin e → ℂ) → ℝ), IsCompatChart A ψ → IsOpen O → O ⊆ ψ.target → ContDiffOn ℝ ∞ G O → A.SmoothOn (ψ.source ∩ ψ ⁻¹' O) (G ∘ ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | exact GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' | (intros; apply GlobalTheory.CompanionTheory.Metric.smoothOn_comp_compatChart' <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmooth

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem locExt_two_le : (2 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

theorem locExt_isOpen_punct {n : ℕ} (R : ℝ) : IsOpen (punct (n := n) R) := by
  have h : punct (n := n) R = ⋂ i, ({z | z i ≠ 0} ∩ {z | ‖z i‖ < R}) := by
    ext z; simp [punct]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_ne_fun (continuous_apply i) continuous_const).inter
      (isOpen_lt (continuous_apply i).norm continuous_const)

theorem locExt_isOpen_nz {n : ℕ} (S : Finset (Fin n)) :
    IsOpen {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} := by
  have h : {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z | z i ≠ 0} := by
    ext z; simp
  rw [h]
  exact isOpen_biInter_finset fun i _ => isOpen_ne_fun (continuous_apply i) continuous_const

theorem locExt_core {n : ℕ} (c : Fin n → ℂ) (r : ℝ) (hr : 0 < r) (Q : Set (Fin n → ℂ))
    (hQ : IsOpen Q) (hcov : ∀ z ∈ Metric.ball c r, (∀ i, z i ≠ c i) → z ∈ Q)
    (F : (Fin n → ℂ) → ℝ) (hsm : ∀ z ∈ Metric.ball c r ∩ Q, ContDiffAt ℝ ∞ F z)
    (hlevi : ∀ z ∈ Metric.ball c r ∩ Q, ∀ w, levi F z w = 0)
    (B : ℝ) (hB : ∀ z ∈ Metric.ball c r ∩ Q, |F z| ≤ B) :
    ∃ G : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ G (Metric.ball c (r / 2)) ∧
      ∀ z ∈ Metric.ball c (r / 2) ∩ Q, G z = F z := by
  set f : (Fin n → ℂ) → ℝ := fun w => F (c + w) with hf
  have hmem : ∀ w ∈ punct (n := n) r, c + w ∈ Metric.ball c r ∩ Q := by
    intro w hw
    have hb : c + w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (pi_norm_lt_iff hr).2 fun i => (hw i).2
    refine ⟨hb, hcov _ hb fun i => ?_⟩
    simpa using (hw i).1
  have hτ : ∀ w : Fin n → ℂ, ContDiffAt ℝ ∞ (fun w : Fin n → ℂ => c + w) w :=
    fun w => contDiffAt_const.add contDiffAt_id
  have hfsm : ∀ w ∈ punct (n := n) r, ContDiffAt ℝ ∞ f w :=
    fun w hw => ContDiffAt.comp w (hsm _ (hmem w hw)) (hτ w)
  have hharm : SepHarm r f := by
    refine GlobalTheory.T.levi_flat_separately_harmonic n f (punct r) (locExt_isOpen_punct r)
      (fun w hw => (hfsm w hw).contDiffWithinAt) ?_
    intro w hw v
    have hA : AnalyticAt ℂ (fun w : Fin n → ℂ => c + w) w := analyticAt_const.add analyticAt_id
    have h2 : ContDiffAt ℝ 2 F (c + w) := (hsm _ (hmem w hw)).of_le locExt_two_le
    have := levi_comp (φ := F) (τ := fun w : Fin n → ℂ => c + w) (z := w) v hA h2
    calc levi f w v = levi (F ∘ fun w : Fin n → ℂ => c + w) w v := rfl
      _ = 0 := by rw [this]; exact hlevi _ (hmem w hw) _
  have hfc : ContinuousOn f (punct r) :=
    fun w hw => (hfsm w hw).continuousAt.continuousWithinAt
  have hpo := GlobalTheory.T.polydisc_poisson_reproduces_harmonic n f (r / 2) r B (half_pos hr) (half_lt_self hr) hfc hharm
    (fun w hw => hB _ (hmem w hw))
  have htor : ∀ θ : Fin n → ℝ, torusPt (r / 2) θ ∈ punct (n := n) r := by
    intro θ i
    have hn : ‖torusPt (r / 2) θ i‖ = r / 2 := by
      simp only [torusPt]
      rw [norm_circleMap_zero, abs_of_pos (half_pos hr)]
    refine ⟨fun h0 => ?_, by rw [hn]; exact half_lt_self hr⟩
    rw [h0, norm_zero] at hn
    linarith
  have hcont : Continuous fun θ : Fin n → ℝ => f (torusPt (r / 2) θ) :=
    hfc.comp_continuous
      (continuous_pi fun i => (continuous_circleMap 0 _).comp (continuous_apply i)) htor
  have hG := GlobalTheory.T.polydisc_poisson_smooth n (r / 2) f (half_pos hr) hcont
  have hGc : ContDiffOn ℝ ∞ (fun z => polyPoisson (r / 2) f (z - c)) (Metric.ball c (r / 2)) := by
    refine ContDiffOn.comp (g := polyPoisson (r / 2) f) (f := fun z : Fin n → ℂ => z - c)
      (t := Metric.ball 0 (r / 2)) hG (contDiff_id.sub contDiff_const).contDiffOn ?_
    intro z hz
    simpa [dist_eq_norm] using hz
  refine ⟨fun z => polyPoisson (r / 2) f (z - c), hGc, ?_⟩
  have hT : Dense {z : Fin n → ℂ | ∀ i, z i ≠ c i} := by
    have h := (GlobalTheory.T.dense_coordinate_torus n).preimage (Homeomorph.subRight c).isOpenMap
    convert h using 1
    ext z
    simp [sub_ne_zero]
  have hD : IsOpen (Metric.ball c (r / 2) ∩ Q) := Metric.isOpen_ball.inter hQ
  have hsub : Metric.ball c (r / 2) ∩ Q ⊆ Metric.ball c r ∩ Q :=
    Set.inter_subset_inter_left _ (Metric.ball_subset_ball (half_le_self hr.le))
  have heq : Set.EqOn (fun z => polyPoisson (r / 2) f (z - c)) F
      ((Metric.ball c (r / 2) ∩ Q) ∩ {z : Fin n → ℂ | ∀ i, z i ≠ c i}) := by
    intro z hz
    have hw : z - c ∈ punct (n := n) (r / 2) := by
      intro i
      refine ⟨sub_ne_zero.2 (hz.2 i), ?_⟩
      have h1 : ‖z - c‖ < r / 2 := by simpa [dist_eq_norm] using hz.1.1
      exact (norm_le_pi_norm (z - c) i).trans_lt h1
    simp only
    rw [hpo _ hw, hf]
    simp
  exact Set.EqOn.of_subset_closure heq
    (hGc.mono Set.inter_subset_left).continuousOn
    (fun z hz => (hsm z (hsub hz)).continuousAt.continuousWithinAt)
    Set.inter_subset_left (hT.open_subset_closure_inter hD)

theorem locExt : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  intro e X _ A L s nb m W hs hsnc th u M hth hu hP hPn hM x
  obtain ⟨ψ, hψ, hxψ, S, hbd⟩ := GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hsnc x
  obtain ⟨hcl, -⟩ := GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc
  let g₀ : X → ℝ := fun y => th.φ x y + u y
  let U' : Set X := th.U x ∩ (bdry s)ᶜ
  have hU' : IsOpen U' := (th.isOpen_U x).inter hcl.isOpen_compl
  have hsm0 : A.SmoothOn U' g₀ := fun j =>
    ((hth.1 x j).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add ((hu j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  have hlz : ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U', ∀ w,
      levi (g₀ ∘ (A.chart j).symm) y w = 0 := by
    intro j y hy w
    have hmemP : y ∈ (A.chart j).target ∩
        (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u).U x ∩ (bdry s)ᶜ) :=
      ⟨hy.1, ⟨hy.2.1, trivial⟩, hy.2.2⟩
    have h1 : 0 ≤ levi (g₀ ∘ (A.chart j).symm) y w := hP x j y hmemP w
    have h2 : 0 ≤ levi (fun z => (-1 : ℝ) * (g₀ ∘ (A.chart j).symm) z) y w :=
      hPn x j y hmemP w
    have hc2 : ContDiffAt ℝ 2 (g₀ ∘ (A.chart j).symm) y :=
      ((hsm0 j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU').mem_nhds hy)).of_le
        locExt_two_le
    have h3 := levi_add_smul (f := fun _ => (0 : ℝ)) (-1) contDiffAt_const hc2 w
    simp only [zero_add] at h3
    rw [h3] at h2
    have h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
    linarith
  have hO₁ : IsOpen (ψ.target ∩ ψ.symm ⁻¹' th.U x) :=
    ψ.isOpen_inter_preimage_symm (th.isOpen_U x)
  have hcO₁ : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' th.U x :=
    ⟨ψ.map_source hxψ, by rw [Set.mem_preimage, ψ.left_inv hxψ]; exact th.mem_U x⟩
  let Q : Set (Fin e → ℂ) := {z | ∀ i ∈ S, z i ≠ 0}
  have hQ : IsOpen Q := locExt_isOpen_nz S
  let S' : Finset (Fin e) := S.filter fun i => ψ x i ≠ 0
  have hQ₂ : IsOpen {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0} := locExt_isOpen_nz S'
  have hcQ₂ : ψ x ∈ {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0} :=
    fun i hi => (Finset.mem_filter.1 hi).2
  obtain ⟨r, hr, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.1 ((hO₁.inter hQ₂).mem_nhds ⟨hcO₁, hcQ₂⟩)
  have hcov : ∀ z ∈ Metric.ball (ψ x) r, (∀ i, z i ≠ ψ x i) → z ∈ Q := by
    intro z hz hne i hi
    by_cases h0 : ψ x i = 0
    · rw [← h0]; exact hne i
    · exact (hball (Metric.ball_subset_closedBall hz)).2 i (Finset.mem_filter.2 ⟨hi, h0⟩)
  have hoff : ∀ z ∈ Metric.ball (ψ x) r ∩ Q, z ∈ ψ.target ∧ ψ.symm z ∈ U' := by
    intro z hz
    have hz1 := (hball (Metric.ball_subset_closedBall hz.1)).1
    refine ⟨hz1.1, hz1.2, fun hb => ?_⟩
    obtain ⟨i, hi, h0⟩ := (hbd _ (ψ.map_target hz1.1)).1 hb
    rw [ψ.right_inv hz1.1] at h0
    exact hz.2 i hi h0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (ψ x) r).exists_bound_of_continuousOn
    (f := th.φ x ∘ ψ.symm) fun z hz =>
      (GlobalTheory.T.smooth_in_compatible_chart e X A ψ (th.U x) (th.φ x) hψ (th.isOpen_U x) (hth.1 x) z (hball hz).1.1
        (hball hz).1.2).continuousAt.continuousWithinAt
  obtain ⟨G, hGs, hGe⟩ := locExt_core (ψ x) r hr Q hQ hcov (g₀ ∘ ψ.symm)
    (fun z hz => GlobalTheory.T.smooth_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 z (hoff z hz).1 (hoff z hz).2)
    (fun z hz => GlobalTheory.T.levi_zero_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 hlz z (hoff z hz).1 (hoff z hz).2)
    (C + M) (fun z hz => by
      have h1 := hC z (Metric.ball_subset_closedBall hz.1)
      have h2 := hM _ (hoff z hz).2.2
      rw [Real.norm_eq_abs] at h1
      exact (abs_add_le _ _).trans (add_le_add h1 h2))
  have hhalf : Metric.ball (ψ x) (r / 2) ⊆ Metric.closedBall (ψ x) r :=
    (Metric.ball_subset_ball (half_le_self hr.le)).trans Metric.ball_subset_closedBall
  have hNU : ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2) ⊆ th.U x := by
    intro y hy
    have h := (hball (hhalf hy.2)).1.2
    rwa [Set.mem_preimage, ψ.left_inv hy.1] at h
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2), fun y => (G ∘ ψ) y - th.φ x y,
    ψ.isOpen_inter_preimage Metric.isOpen_ball, ⟨hxψ, Metric.mem_ball_self (half_pos hr)⟩, ?_, ?_⟩
  · intro j
    have h1 := GlobalTheory.T.smoothOn_of_chart_composition e X A ψ (Metric.ball (ψ x) (r / 2)) G hψ Metric.isOpen_ball
      (fun z hz => (hball (hhalf hz)).1.1) hGs
    exact (h1 j).sub ((hth.1 x j).mono fun y hy => ⟨hy.1, hNU hy.2⟩)
  · intro y hy hyb
    have hz : ψ y ∈ Metric.ball (ψ x) (r / 2) ∩ Q :=
      ⟨hy.2, fun i hi h0 => hyb ((hbd y hy.1).2 ⟨i, hi, h0⟩)⟩
    have h := hGe _ hz
    simp only [Function.comp_apply] at h ⊢
    rw [h, ψ.left_inv hy.1]
    simp [g₀]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmoothStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff

theorem _root_.GlobalTheory.T.bounded_psh_correction_locally_smooth : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt <;> assumption)
end
end
