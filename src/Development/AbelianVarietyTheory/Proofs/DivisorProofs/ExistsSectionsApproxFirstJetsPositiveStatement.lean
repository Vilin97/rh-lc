module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureLowerBoundOnCoverBallsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAtlasBallPartitionCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionSmallFirstJetNormalFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionsFiniteWeightedAtlasStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
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
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSectionOfRapidCauchyDbarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHormanderIterationStepStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyOnCoverBallsLtTopOfSmooth

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem n1_lt_infty_of_isSSec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  intro n Y _ _ _ _ _ ι La _ A C la F0 hF
  unfold n1
  rw [ENNReal.sum_lt_top]
  intro a _
  set i := C.idx a
  set T := (A.chart i).target
  have hT : IsOpen T := (A.chart i).open_target
  have hsub : closedBall (C.c a) (C.r a) ⊆ T := C.sub a
  have hF' : ContDiffOn ℝ ∞ (F0 i ∘ (A.chart i).symm) T := hF.1 i
  have hD : ContinuousOn (fun v => fderiv ℝ (F0 i ∘ (A.chart i).symm) v) T :=
    hF'.continuousOn_fderiv_of_isOpen hT (by simp)
  have hph : ContinuousOn (fun v => A.ph la i ((A.chart i).symm v)) T :=
    (A.smooth_ph la i).continuousOn
  have hcont : ContinuousOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) := by
    refine ContinuousOn.mono ?_ hsub
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_finsetSum _ (fun j _ => ?_)
      refine ContinuousOn.pow (ContinuousOn.norm ?_) 2
      unfold wdb
      refine ContinuousOn.div_const (ContinuousOn.add ?_ (ContinuousOn.mul continuousOn_const ?_)) _
      · exact hD.clm_apply continuousOn_const
      · exact hD.clm_apply continuousOn_const
    · exact (hph.neg).rexp
  have hint : IntegrableOn (fun v => (∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
      Real.exp (-A.ph la i ((A.chart i).symm v))) (closedBall (C.c a) (C.r a)) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  calc _ ≤ ∫⁻ v in closedBall (C.c a) (C.r a), ENNReal.ofReal
        ((∑ j, ‖wdb n j (F0 i ∘ (A.chart i).symm) v‖ ^ 2) *
          Real.exp (-A.ph la i ((A.chart i).symm v))) :=
        lintegral_mono_set ball_subset_closedBall
    _ < ⊤ := hint.lintegral_lt_top

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEnergyOnCoverBallsLtTopOfSmoothStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.dbarEnergyOnCoverBalls_lt_top_of_smooth : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La) (F0 : ι → Y → ℂ), A.IsSSec (A.kap + la) F0 → n1 C la F0 < ⊤ := by
  first | exact @GlobalTheory.n1_lt_infty_of_isSSec | exact GlobalTheory.n1_lt_infty_of_isSSec | (intros; apply GlobalTheory.n1_lt_infty_of_isSSec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoughHormanderEstimateCompactManifold

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.rough_hormander_compact : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K t0 : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), t0 ≤ t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧ n0 A la (F0 - F) ≤ ENNReal.ofReal K * n1 C la F0 := by
  intro n Y _ _ _ _ _ _ ι La _ A C
  obtain ⟨K4, hK4, h4⟩ := GlobalTheory.T.exists_local_hormander_iteration_step n Y ι La A C
  refine ⟨4, 4 * K4 + 1, by norm_num, ?_⟩
  intro la t ht hC F0 hF0
  have tpos : 0 < t := by linarith
  have hq : K4 / t ≤ 1 / 4 := by rw [div_le_iff₀ tpos]; linarith
  have step : ∀ F : {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F},
      ∃ G : {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F},
        n0 A la (F.1 - G.1) ≤ ENNReal.ofReal (1 / 4) * n1 C la F.1 ∧
        n1 C la G.1 ≤ ENNReal.ofReal (1 / 4) * n1 C la F.1 := by
    intro F
    obtain ⟨G, hG, h1, h2⟩ := h4 la t tpos hC F.1 F.2
    have hq' : ENNReal.ofReal (K4 / t) ≤ ENNReal.ofReal (1 / 4) := ENNReal.ofReal_le_ofReal hq
    exact ⟨⟨G, hG⟩, h1.trans (by gcongr), h2.trans (by gcongr)⟩
  choose g hg using step
  let S : ℕ → {F : ι → Y → ℂ // A.IsSSec (A.kap + la) F} := fun m => g^[m] ⟨F0, hF0⟩
  have hS : ∀ m, S (m + 1) = g (S m) := fun m => Function.iterate_succ_apply' g m _
  have hN : n1 C la F0 < ⊤ := GlobalTheory.T.dbarEnergyOnCoverBalls_lt_top_of_smooth n Y ι La A C la F0 hF0
  have hq1 : ENNReal.ofReal (1 / 4) ≤ 1 := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h1 : ∀ m, n1 C la (S m).1 ≤ ENNReal.ofReal ((1 / 4) ^ m) * n1 C la F0 := by
    intro m
    induction m with
    | zero => simp [S]
    | succ m ih =>
      rw [hS]
      refine (hg (S m)).2.trans ?_
      calc ENNReal.ofReal (1 / 4) * n1 C la (S m).1
          ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal ((1 / 4) ^ m) * n1 C la F0) := by
            gcongr
        _ = ENNReal.ofReal ((1 / 4) ^ (m + 1)) * n1 C la F0 := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num), pow_succ']
  have h0 : ∀ m, n0 A la ((S m).1 - (S (m + 1)).1) ≤
      ENNReal.ofReal ((n1 C la F0).toReal / 4 ^ m) := by
    intro m
    rw [hS]
    refine (hg (S m)).1.trans ?_
    refine (mul_le_of_le_one_left (zero_le) hq1).trans ((h1 m).trans (le_of_eq ?_))
    rw [show (n1 C la F0).toReal / 4 ^ m = (1 / 4) ^ m * (n1 C la F0).toReal by
        rw [one_div, inv_pow]; ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hN.ne]
  have hT : Tendsto (fun m => n1 C la (S m).1) atTop (𝓝 0) := by
    have hp : Tendsto (fun m : ℕ => ENNReal.ofReal ((1 / 4 : ℝ) ^ m)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal
        (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num))
      simpa using this
    have hl := ENNReal.Tendsto.mul_const hp (Or.inr hN.ne)
    rw [zero_mul] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
      (fun _ => zero_le) h1
  obtain ⟨G, hG, hfin⟩ := GlobalTheory.T.exists_holomorphicSection_of_rapid_cauchy_dbar n Y ι La A C la t (n1 C la F0).toReal (fun m => (S m).1)
    tpos hC ENNReal.toReal_nonneg (fun m => (S m).2) h0 hT
  refine ⟨G, hG, hfin.trans (le_of_eq ?_)⟩
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hN.ne]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RoughHormanderEstimateCompactManifoldStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.rough_hormander_estimate_compact_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ C : Cover A, ∃ K t0 : ℝ, 0 ≤ K ∧ ∀ (la : La) (t : ℝ), t0 ≤ t → CurvGe C la t → ∀ F0 : ι → Y → ℂ, A.IsSSec (A.kap + la) F0 → ∃ F : ι → Y → ℂ, A.IsSec (A.kap + la) F ∧ n0 A la (F0 - F) ≤ ENNReal.ofReal K * n1 C la F0 := by
  first | exact @GlobalTheory.rough_hormander_compact | exact GlobalTheory.rough_hormander_compact | (intros; apply GlobalTheory.rough_hormander_compact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsApproxFirstJetsPositive

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem jets_approx_sections_of_positive : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ q : Y → V n → ℂ, (∀ P ∈ T, Differentiable ℂ (q P)) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + (G + k • H)) F ∧ ∀ P ∈ T, ‖F (A.pick P) P * Complex.exp (-(k * q P (A.chart (A.pick P) P))) - p P (A.chart (A.pick P) P)‖ ≤ ε ∧ ‖fderiv ℂ (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v) (A.chart (A.pick P) P)‖ ≤ ε := by
  intro n Y _ _ _ _ _ _ ι La _ A H hH T
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_atlasBallPartitionCover n Y ι La A
  obtain ⟨q, c, Cq, r0, hc, hr0, hqT, hrest⟩ := GlobalTheory.T.peak_sections_finite_weighted_atlas n Y ι La A C H hH T
  refine ⟨q, fun P hP => (hqT P hP).1, ?_⟩
  intro G p hp ε hε
  obtain ⟨K', t0, hK', hk6⟩ := GlobalTheory.T.rough_hormander_estimate_compact_manifold n Y ι La A C
  obtain ⟨k1, hk1⟩ := GlobalTheory.T.curvature_lower_bound_on_cover_balls n Y ι La A C H G hH t0
  obtain ⟨K, hK, hF0⟩ := hrest G p hp
  have hloc : ∀ P : Y, ∃ k0 : ℕ, P ∈ T → ∀ k ≥ k0, ∀ D : ι → Y → ℂ,
      A.IsSSec (A.kap + (G + k • H)) D →
      DifferentiableOn ℂ (D (A.pick P) ∘ (A.chart (A.pick P)).symm) (ball (A.chart (A.pick P) P) r0) →
      n0 A (G + k • H) D ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) →
      ‖D (A.pick P) ((A.chart (A.pick P)).symm (A.chart (A.pick P) P)) *
          Complex.exp (-(k * q P (A.chart (A.pick P) P)))‖ ≤ ε ∧
      ‖fderiv ℂ (fun v => D (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)))
          (A.chart (A.pick P) P)‖ ≤ ε := by
    intro P
    by_cases hP : P ∈ T
    · obtain ⟨k0, hk0⟩ := GlobalTheory.T.peak_section_small_first_jet_normal_frame n Y ι La A H G (A.pick P) (A.chart (A.pick P) P) r0 c Cq
        (K' * K) (q P) hr0 hc (hqT P hP).2.1 (hqT P hP).1 (hqT P hP).2.2 ε hε
      exact ⟨k0, fun _ => hk0⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose k0 hk0 using hloc
  refine ⟨max k1 (T.sup k0), fun k hk => ?_⟩
  have hk1' : k1 ≤ k := le_trans (le_max_left _ _) hk
  obtain ⟨F0, hF0s, hF0b, hF0n⟩ := hF0 k
  obtain ⟨F, hFs, hFn⟩ := hk6 (G + k • H) t0 le_rfl (hk1 k hk1') F0 hF0s
  refine ⟨F, hFs, fun P hP => ?_⟩
  have hkP : k0 P ≤ k := le_trans (le_trans (Finset.le_sup hP) (le_max_right _ _)) hk
  have hDs : A.IsSSec (A.kap + (G + k • H)) (F0 - F) := by
    refine ⟨fun j => ?_, fun a b y ha hb => ?_⟩
    · have hd : DifferentiableOn ℂ (F j ∘ (A.chart j).symm) (A.chart j).target :=
        (hFs.1 j).mono fun _ hv => ⟨hv, trivial⟩
      have hF' : ContDiffOn ℝ ∞ (F j ∘ (A.chart j).symm) (A.chart j).target := fun v hv =>
        (hyq_contDiffAt_of_holo (A.chart j).open_target hd hv).contDiffWithinAt
      exact (hF0s.1 j).sub hF'
    · simp only [Pi.sub_apply]
      rw [hF0s.2 a b y ha hb, hFs.2 a b y trivial ha hb]
      ring
  have hb : ball (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target :=
    ball_subset_closedBall.trans (hqT P hP).2.1
  have hDd : DifferentiableOn ℂ ((F0 - F) (A.pick P) ∘ (A.chart (A.pick P)).symm)
      (ball (A.chart (A.pick P) P) r0) := by
    have hg : DifferentiableOn ℂ (fun v => p P v * Complex.exp (k * q P v) -
        F (A.pick P) ((A.chart (A.pick P)).symm v)) (ball (A.chart (A.pick P) P) r0) := by
      refine DifferentiableOn.sub ?_ ?_
      · exact ((hp P).mul (((hqT P hP).1.const_mul _).cexp)).differentiableOn
      · exact (hFs.1 (A.pick P)).mono fun v hv => ⟨hb hv, trivial⟩
    refine hg.congr fun v hv => ?_
    simp only [Function.comp_apply, Pi.sub_apply]
    rw [hF0b P hP v hv]
  have hDn : n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal ((K' * K) * Real.exp (-c * k)) := by
    calc n0 A (G + k • H) (F0 - F) ≤ ENNReal.ofReal K' * n1 C (G + k • H) F0 := hFn
      _ ≤ ENNReal.ofReal K' * ENNReal.ofReal (K * Real.exp (-c * k)) := by gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul hK', mul_assoc]
  obtain ⟨h1, h2⟩ := hk0 P hP k hkP (F0 - F) hDs hDd hDn
  have key : ∀ v ∈ ball (A.chart (A.pick P) P) r0,
      F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v =
        -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v))) := by
    intro v hv
    have h0 := hF0b P hP v hv
    have hE : Complex.exp (k * q P v) * Complex.exp (-(k * q P v)) = 1 := by
      rw [← Complex.exp_add]; simp
    simp only [Pi.sub_apply]
    rw [h0]
    linear_combination p P v * hE
  have hPx : (A.chart (A.pick P)).symm (A.chart (A.pick P) P) = P :=
    (A.chart (A.pick P)).left_inv (A.mem_pick P)
  have hx : A.chart (A.pick P) P ∈ ball (A.chart (A.pick P) P) r0 := mem_ball_self hr0
  refine ⟨?_, ?_⟩
  · have h3 := key _ hx
    rw [hPx] at h3 h1
    rw [h3, norm_neg]
    exact h1
  · have hev : (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v)
        =ᶠ[𝓝 (A.chart (A.pick P) P)]
        fun v => -((F0 - F) (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v))) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with v hv using key v hv
    rw [hev.fderiv_eq, fderiv_fun_neg, norm_neg]
    exact h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsApproxFirstJetsPositiveStatement

section

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_sections_approx_firstJets_positive : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ q : Y → V n → ℂ, (∀ P ∈ T, Differentiable ℂ (q P)) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∃ F : ι → Y → ℂ, A.IsSec (A.kap + (G + k • H)) F ∧ ∀ P ∈ T, ‖F (A.pick P) P * Complex.exp (-(k * q P (A.chart (A.pick P) P))) - p P (A.chart (A.pick P) P)‖ ≤ ε ∧ ‖fderiv ℂ (fun v => F (A.pick P) ((A.chart (A.pick P)).symm v) * Complex.exp (-(k * q P v)) - p P v) (A.chart (A.pick P) P)‖ ≤ ε := by
  first | exact @GlobalTheory.jets_approx_sections_of_positive | exact GlobalTheory.jets_approx_sections_of_positive | (intros; apply GlobalTheory.jets_approx_sections_of_positive <;> assumption)
end
end
