module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeakSectionSmallDbarEnergyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Max
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshNormalFrameQuadraticComparisonStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinSumSmoothSectionDbarEnergyLe

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isSSec_finset_sum_and_n1_le_card_mul_sum (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ)
    (hF : ∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) :
    A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧
      n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  refine ⟨⟨fun i => ?_, fun i j y hi hj => ?_⟩, ?_⟩
  · exact ContDiffOn.sum (fun P hP => (hF P hP).1 i)
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun P hP => (hF P hP).2 i j y hi hj)
  ·
    have key : ∀ a : Fin C.m,
        (∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P (C.idx a) y) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))))
        ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) := by
      intro a
      set i := C.idx a with hi
      set e := A.chart i with he
      have hball : Metric.ball (C.c a) (C.r a) ⊆ e.target :=
        Metric.ball_subset_closedBall.trans (C.sub a)
      have hdiff : ∀ P ∈ T, ∀ v ∈ Metric.ball (C.c a) (C.r a),
          DifferentiableAt ℝ (F P i ∘ e.symm) v := fun P hP v hv =>
        ((hF P hP).1 i).differentiableOn (by simp) |>.differentiableAt
          (e.open_target.mem_nhds (hball hv))

      have hcont : ∀ P ∈ T, ContinuousOn (fun v => ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))) (Metric.ball (C.c a) (C.r a)) := by
        intro P hP
        have hfd : ContinuousOn (fderiv ℝ (F P i ∘ e.symm)) e.target :=
          ((hF P hP).1 i).continuousOn_fderiv_of_isOpen e.open_target (by simp)
        have hph : ContinuousOn (fun v => A.ph la i (e.symm v)) e.target :=
          (A.smooth_ph la i).continuousOn
        refine ENNReal.continuous_ofReal.comp_continuousOn ?_
        refine ContinuousOn.mul ?_ ((hph.mono hball).neg.rexp)
        refine continuousOn_finsetSum _ (fun j _ => ?_)
        refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
        unfold wdb
        refine ContinuousOn.div_const (ContinuousOn.add ?_ (continuousOn_const.mul ?_)) _
        · exact (hfd.clm_apply continuousOn_const).mono hball
        · exact (hfd.clm_apply continuousOn_const).mono hball
      have hpt : ∀ v ∈ Metric.ball (C.c a) (C.r a),
          ENNReal.ofReal ((∑ j, ‖wdb n j ((fun y => ∑ P ∈ T, F P i y) ∘ e.symm) v‖ ^ 2) *
            Real.exp (-A.ph la i (e.symm v)))
          ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) := by
        intro v hv
        have hfun : (fun y => ∑ P ∈ T, F P i y) ∘ e.symm = fun w => ∑ P ∈ T, (F P i ∘ e.symm) w := rfl
        rw [hfun]
        have hs : ∀ j, wdb n j (fun w => ∑ P ∈ T, (F P i ∘ e.symm) w) v
            = ∑ P ∈ T, wdb n j (F P i ∘ e.symm) v := fun j => wdb_sum T (fun P hP => hdiff P hP v hv)
        simp only [hs]
        have hE := Real.exp_pos (-A.ph la i (e.symm v))
        have hreal : (∑ j, ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))
            ≤ (T.card : ℝ) * ∑ P ∈ T, (∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) *
              Real.exp (-A.ph la i (e.symm v)) := by
          rw [← Finset.sum_mul, ← mul_assoc, Finset.sum_comm, Finset.mul_sum]
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) hE.le
          calc ‖∑ P ∈ T, wdb n j (F P i ∘ e.symm) v‖ ^ 2
              ≤ (∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
            _ ≤ (T.card : ℝ) * ∑ P ∈ T, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2 :=
                sq_sum_le_card_mul_sum_sq
        refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun P _ => by positivity)]
      calc _ ≤ ∫⁻ v in Metric.ball (C.c a) (C.r a), (T.card : ℝ≥0∞) * ∑ P ∈ T, ENNReal.ofReal
            ((∑ j, ‖wdb n j (F P i ∘ e.symm) v‖ ^ 2) * Real.exp (-A.ph la i (e.symm v))) :=
            lintegral_mono_ae ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
              (Filter.Eventually.of_forall hpt))
        _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
            lintegral_finsetSum' _ (fun P hP => (hcont P hP).aemeasurable
              Metric.isOpen_ball.measurableSet)]
    unfold n1
    calc _ ≤ ∑ a, (T.card : ℝ≥0∞) * ∑ P ∈ T, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
          ((∑ j, ‖wdb n j (F P (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
            Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v))) :=
          Finset.sum_le_sum fun a _ => key a
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end GlobalTheory.OTY
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinSumSmoothSectionDbarEnergyLeStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.finSum_smoothSection_dbarEnergy_le : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (T : Finset Y) (F : Y → ι → Y → ℂ), (∀ P ∈ T, A.IsSSec (A.kap + la) (F P)) → A.IsSSec (A.kap + la) (fun i y => ∑ P ∈ T, F P i y) ∧ n1 C la (fun i y => ∑ P ∈ T, F P i y) ≤ (T.card : ℝ≥0∞) * ∑ P ∈ T, n1 C la (F P) := by
  first | exact @GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum | exact GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum | (intros; apply GlobalTheory.OTY.isSSec_finset_sum_and_n1_le_card_mul_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosLowerBoundOnFinset

section

@[expose] public section

namespace GlobalTheory.PositiveLowerBoundFinset

theorem pos_lower_bound_on_finset : ∀ {Y : Type} (T : Finset Y) (f : Y → ℝ),
    (∀ (P : Y), (0 : ℝ) < f P) → ∃ (r : ℝ), (0 : ℝ) < r ∧ ∀ P ∈ T, r ≤ f P := by
  intro Y T f hf
  rcases T.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x, -, hmin⟩ := T.exists_min_image f h
    exact ⟨f x, hf x, hmin⟩

end GlobalTheory.PositiveLowerBoundFinset
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionsFiniteWeightedAtlas

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peakFin_exists_pos_le {Y : Type} (T : Finset Y) (f : Y → ℝ) (hf : ∀ P, 0 < f P) :
    ∃ r : ℝ, 0 < r ∧ ∀ P ∈ T, r ≤ f P := by
  first
  | exact @_root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
  | exact _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
  | (apply _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset ..)

theorem peak_sections_finite : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ (q : Y → V n → ℂ) (c Cq r0 : ℝ), 0 < c ∧ 0 < r0 ∧ (∀ P ∈ T, Differentiable ℂ (q P) ∧ closedBall (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target ∧ ∀ v ∈ closedBall (A.chart (A.pick P) P) r0, A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q P v).re ≤ Cq * ‖v - (A.chart (A.pick P) P)‖ ^ 2) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ P ∈ T, ∀ v ∈ ball (A.chart (A.pick P) P) r0, F0 (A.pick P) ((A.chart (A.pick P)).symm v) = p P v * Complex.exp (k * q P v)) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-c * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H hH T
  classical
  obtain ⟨U, hU, hdisj⟩ := T.finite_toSet.t2_separation
  have h7 : ∀ P : Y, ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧
      closedBall (A.chart (A.pick P) P) ρ ⊆
        (A.chart (A.pick P)).target ∩ (A.chart (A.pick P)).symm ⁻¹' U P ∧
      ∀ v ∈ closedBall (A.chart (A.pick P) P) ρ,
        c * ‖v - A.chart (A.pick P) P‖ ^ 2 ≤
          A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q v).re ∧
        A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q v).re ≤
          C * ‖v - A.chart (A.pick P) P‖ ^ 2 := by
    intro P
    refine GlobalTheory.T.psh_normal_frame_quadratic_comparison n _ (fun v => A.ph H (A.pick P) ((A.chart (A.pick P)).symm v)) _
      ((A.chart (A.pick P)).isOpen_inter_preimage_symm (hU P).2) ?_
      ((A.smooth_ph H (A.pick P)).mono Set.inter_subset_left) ?_
    · refine ⟨(A.chart (A.pick P)).map_source (A.mem_pick P), ?_⟩
      rw [Set.mem_preimage, (A.chart (A.pick P)).left_inv (A.mem_pick P)]
      exact (hU P).1
    · intro ξ hξ
      exact hH (A.pick P) P (A.mem_pick P) ξ hξ
  choose q c Cc ρ hq hc hC hρ hsub hb using h7
  obtain ⟨r0, hr0, hr0le⟩ := peakFin_exists_pos_le T (fun P => ρ P / 2)
    (fun P => half_pos (hρ P))
  obtain ⟨c0, hc0, hc0le⟩ := peakFin_exists_pos_le T (fun P => c P * ρ P ^ 2 / 4)
    (fun P => by have := hc P; have := hρ P; positivity)
  have hrρ : ∀ P ∈ T, r0 ≤ ρ P := fun P hP => by
    have h1 : r0 ≤ ρ P / 2 := hr0le P hP
    have := hρ P
    linarith
  refine ⟨q, c0, ∑ P ∈ T, Cc P, r0, hc0, hr0, fun P hP => ⟨hq P, ?_, ?_⟩, ?_⟩
  · exact ((closedBall_subset_closedBall (hrρ P hP)).trans (hsub P)).trans Set.inter_subset_left
  · intro v hv
    refine (hb P v (closedBall_subset_closedBall (hrρ P hP) hv)).2.trans ?_
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := Cc) (fun Q _ => (hC Q).le) hP) (by positivity)
  · intro G p hp
    have h9 := fun P : Y => GlobalTheory.T.exists_peak_section_small_dbar_energy n Y ι La A C H G (A.pick P) (A.chart (A.pick P) P)
      (ρ P) (c P) (q P) (p P) (hρ P) (hc P) ((hsub P).trans Set.inter_subset_left) (hq P) (hp P)
      (fun v hv => (hb P v hv).1)
    choose K hK F hF using h9
    have hKs : 0 ≤ ∑ P ∈ T, K P := Finset.sum_nonneg fun P _ => hK P
    refine ⟨(T.card : ℝ) * ∑ P ∈ T, K P, by positivity, fun k => ?_⟩
    obtain ⟨hs, hn⟩ := GlobalTheory.T.finSum_smoothSection_dbarEnergy_le n Y ι La A C (G + k • H) T (fun P => F P k)
      (fun P _ => (hF P k).1)
    refine ⟨_, hs, fun P hP v hv => ?_, hn.trans ?_⟩
    · have hv' : v ∈ ball (A.chart (A.pick P) P) (ρ P / 2) := ball_subset_ball (hr0le P hP) hv
      have hvU : (A.chart (A.pick P)).symm v ∈ U P :=
        (hsub P (ball_subset_closedBall (ball_subset_ball (hrρ P hP) hv))).2
      rw [← (hF P k).2.1 v hv']
      refine Finset.sum_eq_single_of_mem P hP (fun Q hQ hQP => ?_)
      refine (hF Q k).2.2.1 _ _ (fun hm => ?_)
      have h1 := (hsub Q (ball_subset_closedBall hm.2)).2
      rw [Set.mem_preimage, (A.chart (A.pick Q)).left_inv hm.1] at h1
      exact Set.disjoint_left.1 (hdisj (Finset.mem_coe.2 hQ) (Finset.mem_coe.2 hP) hQP) h1 hvU
    · have hle : ∑ P ∈ T, n1 C (G + k • H) (F P k) ≤
          ∑ P ∈ T, ENNReal.ofReal (K P * Real.exp (-c0 * k)) := by
        refine Finset.sum_le_sum fun P hP => (hF P k).2.2.2.trans ?_
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hK P))
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))
        exact neg_le_neg (hc0le P hP)
      refine (mul_le_mul_right hle _).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun P _ => mul_nonneg (hK P) (Real.exp_pos _).le), ← Finset.sum_mul, mul_assoc,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end GlobalTheory.OTY
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionsFiniteWeightedAtlasStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.peak_sections_finite_weighted_atlas : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ (q : Y → V n → ℂ) (c Cq r0 : ℝ), 0 < c ∧ 0 < r0 ∧ (∀ P ∈ T, Differentiable ℂ (q P) ∧ closedBall (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target ∧ ∀ v ∈ closedBall (A.chart (A.pick P) P) r0, A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q P v).re ≤ Cq * ‖v - (A.chart (A.pick P) P)‖ ^ 2) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ P ∈ T, ∀ v ∈ ball (A.chart (A.pick P) P) r0, F0 (A.pick P) ((A.chart (A.pick P)).symm v) = p P v * Complex.exp (k * q P v)) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-c * k)) := by
  first | exact @GlobalTheory.OTY.peak_sections_finite | exact GlobalTheory.OTY.peak_sections_finite | (intros; apply GlobalTheory.OTY.peak_sections_finite <;> assumption)
end
end
