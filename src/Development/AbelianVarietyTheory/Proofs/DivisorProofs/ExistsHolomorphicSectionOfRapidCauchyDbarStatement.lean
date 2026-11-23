module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloAeEqStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesSectionsL2LimitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HormanderEstimateOnBallConstLeviBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPartStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloSectionAeEqOfBallCover

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.AeHoloGlue

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem mu_ne_zero_of_open (A : WeightedAtlas n Y ι La) {O : Set Y} (hO : IsOpen O)
    (hne : O.Nonempty) : A.mu O ≠ 0 := by
  obtain ⟨y, hy⟩ := hne
  have hW : IsOpen (O ∩ (A.chart (A.pick y)).source) := hO.inter (A.chart (A.pick y)).open_source
  have hWs : O ∩ (A.chart (A.pick y)).source ⊆ (A.chart (A.pick y)).source := Set.inter_subset_right
  have hS : IsOpen (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) :=
    (A.chart (A.pick y)).isOpen_image_of_subset_source hW hWs
  have hSne : (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ ⟨hy, A.mem_pick y⟩⟩
  have hSt : A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source) ⊆ (A.chart (A.pick y)).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart (A.pick y)).map_source hx.2
  intro h0
  have h1 : A.mu (O ∩ (A.chart (A.pick y)).source) = 0 := measure_mono_null Set.inter_subset_left h0
  rw [A.mu_chart _ _ hW.measurableSet hWs] at h1
  have hc : ContinuousOn (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v))))
      (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) := by
    have := (A.smooth_ph A.kap (A.pick y)).continuousOn.mono hSt
    exact ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn this)
  rw [lintegral_eq_zero_iff' (hc.aemeasurable hS.measurableSet)] at h1
  have h3 := ae_iff.mp h1
  have hu : {v | ¬ (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v)))) v
      = (0 : V n → ℝ≥0∞) v} = Set.univ := by
    ext v; simp [ENNReal.ofReal_eq_zero, Real.exp_pos]
  rw [hu, Measure.restrict_apply_univ] at h3
  exact hS.measure_ne_zero volume hSne h3

theorem exists_null (A : WeightedAtlas n Y ι La) (i : ι) (c : V n) (r : ℝ) (u : V n → ℂ)
    (f : Y → ℂ) (h : u =ᵐ[volume.restrict (ball c r)] f ∘ (A.chart i).symm) :
    ∃ M : Set Y, A.mu M = 0 ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball c r → y ∉ M →
      u (A.chart i y) = f y := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at h
  obtain ⟨T, hET, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  classical
  have hφ : Measurable ((A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n))) :=
    ContinuousOn.measurable_piecewise (A.chart i).continuousOn continuousOn_const
      (A.chart i).open_source.measurableSet
  refine ⟨(A.chart i).source ∩ (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T,
    ?_, ?_⟩
  · have hm : MeasurableSet ((A.chart i).source ∩
        (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T) :=
      (A.chart i).open_source.measurableSet.inter (hφ hTm)
    rw [A.mu_chart i _ hm Set.inter_subset_left]
    refine le_antisymm ?_ (by simp)
    calc _ ≤ ∫⁻ v in T, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
          apply lintegral_mono_set
          rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
          have : (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) x = A.chart i x :=
            Set.piecewise_eq_of_mem _ _ _ hx1
          simpa [this] using hx2
      _ = 0 := setLIntegral_measure_zero _ _ hT0
  · intro y hy hb hM
    by_contra hne
    apply hM
    refine ⟨hy, ?_⟩
    show (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) y ∈ T
    rw [Set.piecewise_eq_of_mem _ _ _ hy]
    apply hET
    simp only [Set.mem_setOf_eq]
    intro heq
    apply hne
    simpa [Function.comp, (A.chart i).left_inv hy] using heq hb

theorem continuousOn_g (A : WeightedAtlas n Y ι La) (la : La) (i j : ι) :
    ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
  have h1 : ContinuousOn (A.g la i j ∘ (A.chart i).symm ∘ A.chart i)
      ((A.chart i).source ∩ (A.chart j).source) := by
    refine (A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left) ?_
    intro y hy
    exact ⟨(A.chart i).map_source hy.1, by simpa [(A.chart i).left_inv hy.1] using hy.2⟩
  refine h1.congr ?_
  intro y hy
  simp [(A.chart i).left_inv hy.1]

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La),
    ∀ (C : Cover A) (la : La) (f : ι → Y → ℂ) (u : Fin C.m → V n → ℂ),
    (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g la i j y * f j y) →
    (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    (∀ a, u a =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm) →
    ∃ F : ι → Y → ℂ, A.IsSec la F ∧ ∀ᵐ y ∂A.mu, F (A.pick y) y = f (A.pick y) y := by
  intro n Y _ _ _ _ _ ι La _ A C la f u hf hu hae
  classical

  have hBo : ∀ a, IsOpen ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :=
    fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hcov : ∀ y, ∃ a, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) := by
    intro y
    by_contra hno
    push_neg at hno
    have h0 : ∀ a, C.chi a y = 0 := fun a => by
      by_contra hne
      exact hno a (C.supp a (subset_tsupport _ hne))
    have := C.sum_one y
    simp [h0] at this
  choose M hM0 hM using fun a => exists_null A (C.idx a) (C.c a) (C.r a) (u a) (f (C.idx a)) (hae a)
  have hM0' : A.mu (⋃ a, M a) = 0 := measure_iUnion_null hM0

  have hoff : ∀ a y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∉ ⋃ a, M a → u a (A.chart (C.idx a) y) = f (C.idx a) y := fun a y hy hn =>
    hM a y hy.1 hy.2 (fun h => hn (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hcu : ∀ a, ContinuousOn (fun y => u a (A.chart (C.idx a) y))
      ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) := fun a =>
    (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
      (fun y hy => hy.2)

  have hagree : ∀ a b y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∈ (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b) →
      u a (A.chart (C.idx a) y) = A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y) := by
    intro a b y hya hyb
    set D := ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) ∩
      ((A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b)) with hD
    have hcont : ContinuousOn (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) D :=
      ((hcu a).mono Set.inter_subset_left).sub
        (((continuousOn_g A la (C.idx a) (C.idx b)).mono
          (show D ⊆ (A.chart (C.idx a)).source ∩ (A.chart (C.idx b)).source from
            fun z hz => ⟨hz.1.1, hz.2.1⟩)).mul ((hcu b).mono Set.inter_subset_right))
    have hop := hcont.isOpen_inter_preimage ((hBo a).inter (hBo b)) (isOpen_compl_singleton (x := (0 : ℂ)))
    have hsub : D ∩ (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) ⁻¹' {0}ᶜ ⊆ ⋃ a, M a := by
      intro z ⟨hz, hz0⟩
      by_contra hn
      apply hz0
      simp only [Set.mem_singleton_iff]
      rw [hoff a z hz.1 hn, hoff b z hz.2 hn, hf _ _ z hz.1.1 hz.2.1]
      ring
    by_contra hne
    exact mu_ne_zero_of_open A hop ⟨y, ⟨hya, hyb⟩, by simpa [sub_eq_zero] using hne⟩
      (measure_mono_null hsub hM0')
  choose α hα using hcov
  refine ⟨fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y), ⟨?_, ?_⟩, ?_⟩
  ·
    intro i v hv
    have hvs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv.1
    set a0 := α ((A.chart i).symm v)
    have hO : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      (A.chart i).isOpen_inter_preimage_symm (hBo a0)
    have hvO : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) :=
      ⟨hv.1, hα _⟩
    have hOovl : (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) ⊆
        ovl A.chart i (C.idx a0) := fun w hw => ⟨hw.1, hw.2.1⟩
    have hG : DifferentiableOn ℂ (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
          ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      ((A.holo_g la i (C.idx a0)).mono hOovl).mul
        ((hu a0).comp ((A.holo_trans i (C.idx a0)).mono hOovl) (fun w hw => hw.2.2))
    have hloc : (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w)) =ᶠ[𝓝 v]
        ((fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y)) i ∘
          (A.chart i).symm) := by
      filter_upwards [hO.mem_nhds hvO] with w hw
      have hws : (A.chart i).symm w ∈ (A.chart i).source := (A.chart i).map_target hw.1
      simp only [Function.comp]
      rw [hagree (α ((A.chart i).symm w)) a0 _ (hα _) hw.2, ← mul_assoc,
        ← A.g_cocycle la i _ _ _ hws (hα _).1 hw.2.1]
    exact ((hG.differentiableAt (hO.mem_nhds hvO)).congr_of_eventuallyEq hloc.symm).differentiableWithinAt
  ·
    intro i j y _ hi hj
    simp only
    rw [A.g_cocycle la i j (C.idx (α y)) y hi hj (hα y).1]
    ring
  ·
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hM0'] with y hy
    rw [hoff _ y (hα y) hy, ← hf _ _ y (A.mem_pick y) (hα y).1]

end GlobalTheory.AeHoloGlue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloSectionAeEqOfBallCoverStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_holo_section_ae_eq_of_ball_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (f : ι → Y → ℂ) (u : Fin C.m → V n → ℂ), (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g la i j y * f j y) → (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) → (∀ a, u a =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm) → ∃ F : ι → Y → ℂ, A.IsSec la F ∧ ∀ᵐ y ∂A.mu, F (A.pick y) y = f (A.pick y) y := by
  first | exact @GlobalTheory.AeHoloGlue.main | exact GlobalTheory.AeHoloGlue.main | (intros; apply GlobalTheory.AeHoloGlue.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSectionOfRapidCauchyDbar

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem ofReal_sq_sub_mul_le (x y z : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (‖x - y‖ ^ 2 * ρ) ≤
      2 * ENNReal.ofReal (‖z - x‖ ^ 2 * ρ) + 2 * ENNReal.ofReal (‖z - y‖ ^ 2 * ρ) := by
  have h1 : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
    calc ‖x - y‖ = ‖(z - y) - (z - x)‖ := by congr 1; ring
      _ ≤ ‖z - y‖ + ‖z - x‖ := norm_sub_le _ _
      _ = ‖z - x‖ + ‖z - y‖ := add_comm _ _
  have h2 : ‖x - y‖ ^ 2 ≤ 2 * ‖z - x‖ ^ 2 + 2 * ‖z - y‖ ^ 2 := by
    nlinarith [norm_nonneg (x - y), norm_nonneg (z - x), norm_nonneg (z - y),
      sq_nonneg (‖z - x‖ - ‖z - y‖)]
  have h3 : ‖x - y‖ ^ 2 * ρ ≤ 2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ) := by
    have := mul_le_mul_of_nonneg_right h2 hρ
    linarith
  calc ENNReal.ofReal (‖x - y‖ ^ 2 * ρ)
      ≤ ENNReal.ofReal (2 * (‖z - x‖ ^ 2 * ρ) + 2 * (‖z - y‖ ^ 2 * ρ)) := ENNReal.ofReal_le_ofReal h3
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp

theorem exists_isSec_of_rapid_cauchy : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (t K : ℝ) (F : ℕ → ι → Y → ℂ), 0 < t → CurvGe C la t → 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → Tendsto (fun m => n1 C la (F m)) atTop (𝓝 0) → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + la) G ∧ n0 A la (F 0 - G) ≤ ENNReal.ofReal (4 * K) := by
  intro n Y _ _ _ _ _ ι La _ A C la t K F ht hcurv hK hF hcau hn1
  obtain ⟨f, hfc, hfm, hfn⟩ := GlobalTheory.T.geometric_series_sections_l2_limit n Y ι La A la F K hK hF hcau

  have hWsub : ∀ a, ball (C.c a) (C.r a) ⊆ (A.chart (C.idx a)).target :=
    fun a => ball_subset_closedBall.trans (C.sub a)

  have hH : ∀ m a, ∃ u : V n → ℂ, DifferentiableOn ℂ u (ball (C.c a) (C.r a)) ∧
      ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u v‖ ^ 2 *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) ≤ ENNReal.ofReal t⁻¹ * n1 C la (F m) := by
    intro m a
    obtain ⟨u, hu, hle⟩ := GlobalTheory.T.hormander_estimate_on_ball_const_levi_bound n (C.c a) (C.r a) t
      (fun w => A.ph la (C.idx a) ((A.chart (C.idx a)).symm w)) (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) ht
      ((A.smooth_ph la (C.idx a)).mono (hWsub a)) (((hF m).1 (C.idx a)).mono (hWsub a))
      (by
        intro v hv ξ
        have := hcurv a v hv ξ
        simp only [WeightedAtlas.leviAt] at this
        rwa [(A.chart (C.idx a)).right_inv (hWsub a hv)] at this)
    refine ⟨u, hu, hle.trans ?_⟩
    gcongr
    unfold n1
    exact Finset.single_le_sum (f := fun a => ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
      ((∑ j, ‖wdb n j (F m (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
        Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) (fun _ _ => bot_le) (Finset.mem_univ a)
  choose u hu hule using hH

  have hD : ∀ m a, ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) -
      f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 * Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
      ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
    intro m a
    have e := GlobalTheory.T.lintegral_nsq_canonical_add_chart_part n Y ι La A la (C.idx a) (ball (C.c a) (C.r a)) (F m - f) measurableSet_ball (hWsub a)
      (by
        intro y hy _
        simp only [Pi.sub_apply]
        rw [(hF m).2 _ _ _ (A.mem_pick y) hy, hfc _ _ _ (A.mem_pick y) hy]
        ring)
      (((((hF m).1 (C.idx a)).continuousOn.aemeasurable (A.chart (C.idx a)).open_target.measurableSet).sub
        (hfm (C.idx a))).mono_measure (Measure.restrict_mono (hWsub a) le_rfl))
    refine le_trans (le_of_eq e.symm) ?_
    exact (setLIntegral_le_lintegral _ _).trans (hfn m)
  have hT : Tendsto (fun m : ℕ => 2 * ENNReal.ofReal (4 * K / 4 ^ m) +
      2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal (4 * K / 4 ^ m)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal
        (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
    have h2 : Tendsto (fun m => ENNReal.ofReal t⁻¹ * n1 C la (F m)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hn1 (Or.inr ENNReal.ofReal_ne_top)
    simpa using (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top)).add
      (ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofNat_ne_top))

  have hG : ∀ a, ∃ g : V n → ℂ, DifferentiableOn ℂ g (ball (C.c a) (C.r a)) ∧
      g =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm := by
    intro a
    have hρ : ContinuousOn (fun v => Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        (ball (C.c a) (C.r a)) :=
      Real.continuous_exp.comp_continuousOn
        (((A.smooth_ph la (C.idx a)).continuousOn.mono (hWsub a)).neg)
    refine GlobalTheory.T.exists_differentiableOn_ae_eq_of_weighted_L2_limit n (ball (C.c a) (C.r a)) _ (fun m => u m a)
      (f (C.idx a) ∘ (A.chart (C.idx a)).symm) isOpen_ball hρ (fun v _ => Real.exp_pos _)
      (fun m => hu m a) ((hfm (C.idx a)).mono_measure (Measure.restrict_mono (hWsub a) le_rfl)) ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le) ?_
    intro m
    have hY : AEMeasurable (fun v => 2 * ENNReal.ofReal
        (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        (volume.restrict (ball (C.c a) (C.r a))) := by
      refine AEMeasurable.const_mul ?_ _
      refine ContinuousOn.aemeasurable ?_ measurableSet_ball
      refine ENNReal.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.mul ?_ hρ
      refine ContinuousOn.pow ?_ 2
      refine ContinuousOn.norm ?_
      exact ((((hF m).1 (C.idx a)).continuousOn.mono (hWsub a))).sub (hu m a).continuousOn
    calc ∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal (‖(f (C.idx a) ∘ (A.chart (C.idx a)).symm) v - u m a v‖ ^ 2 *
          Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))
        ≤ ∫⁻ v in ball (C.c a) (C.r a), (2 * ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) +
          2 * ENNReal.ofReal (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) :=
          lintegral_mono (fun v => ofReal_sq_sub_mul_le _ _ _ _ (Real.exp_pos _).le)
      _ = 2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - f (C.idx a) ((A.chart (C.idx a)).symm v)‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) +
          2 * (∫⁻ v in ball (C.c a) (C.r a), ENNReal.ofReal
            (‖F m (C.idx a) ((A.chart (C.idx a)).symm v) - u m a v‖ ^ 2 *
              Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))) := by
          rw [lintegral_add_right' _ hY, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      _ ≤ 2 * ENNReal.ofReal (4 * K / 4 ^ m) + 2 * (ENNReal.ofReal t⁻¹ * n1 C la (F m)) := by
          gcongr
          · exact hD m a
          · exact hule m a
  choose g hg hgae using hG
  obtain ⟨G, hGs, hGae⟩ := GlobalTheory.T.exists_holo_section_ae_eq_of_ball_cover n Y ι La A C (A.kap + la) f g hfc hg hgae
  refine ⟨G, hGs, ?_⟩
  have e : n0 A la (F 0 - G) = n0 A la (F 0 - f) := by
    unfold n0
    apply lintegral_congr_ae
    filter_upwards [hGae] with y hy
    simp only [WeightedAtlas.nsq, Pi.sub_apply, hy]
  rw [e]
  simpa using hfn 0

end GlobalTheory.OTY
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSectionOfRapidCauchyDbarStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_holomorphicSection_of_rapid_cauchy_dbar : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (t K : ℝ) (F : ℕ → ι → Y → ℂ), 0 < t → CurvGe C la t → 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → Tendsto (fun m => n1 C la (F m)) atTop (𝓝 0) → ∃ G : ι → Y → ℂ, A.IsSec (A.kap + la) G ∧ n0 A la (F 0 - G) ≤ ENNReal.ofReal (4 * K) := by
  first | exact @GlobalTheory.OTY.exists_isSec_of_rapid_cauchy | exact GlobalTheory.OTY.exists_isSec_of_rapid_cauchy | (intros; apply GlobalTheory.OTY.exists_isSec_of_rapid_cauchy <;> assumption)
end
end
