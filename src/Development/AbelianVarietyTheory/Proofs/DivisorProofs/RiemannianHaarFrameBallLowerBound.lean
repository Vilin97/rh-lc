module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateChartBallDistortion
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.SpanPowerMembership.LeOfEventuallyDown
import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbittAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieHaarLeTwoMulTangentNormalizedHaar

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowDens

open Filter Topology Metric Set GlobalTheory.SUVol.DensOne
open scoped NNReal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lam_le_two_mul_tangentHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → lam s ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
  intro E _ _ _ r Ψ G hG lam _
  obtain ⟨hH, hD⟩ := tangentHaar_realSU_of_det Ψ G hG lam
  generalize tangentHaar (realSU Ψ G) (lam.map Subtype.val) = μ at hH hD ⊢
  let ι : realLie Ψ G →ₗᵢ[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    ⟨(incl Ψ G).toLinearMap, fun X => norm_incl Ψ G X⟩
  let L₀ : (Ψ → Matrix (Fin r) (Fin r) ℂ) →ₗ[ℝ]
      ((Ψ → Matrix (Fin r) (Fin r) ℂ) →L[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have he : Continuous (chartExp Ψ G hG) := continuous_chartExp Ψ G hG
  have he0 : chartExp Ψ G hG 0 = 1 := chartExp_zero Ψ G hG
  have hd : HasStrictFDerivAt (fun x => matR Ψ G (chartExp Ψ G hG x)) ι.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_chart Ψ G hG
  have hL : ContinuousAt (fun g => L₀ (matR Ψ G g)) 1 := (hL₀.comp (continuous_matR Ψ G)).continuousAt
  have hL1 : (fun g => L₀ (matR Ψ G g)) 1 = ContinuousLinearMap.id ℝ _ := by ext1 A; exact one_mul A
  have hm : ∀ g h, matR Ψ G (g * h) = (fun g => L₀ (matR Ψ G g)) g (matR Ψ G h) := fun g h => rfl
  have hn : ∀ ρ : ℝ, 0 < ρ → chartExp Ψ G hG '' ball 0 ρ ∈ 𝓝 (1 : realSU Ψ G) := fun ε hε =>
    (tendsto_iff_comap.1 ((continuous_matR Ψ G).tendsto 1))
      (eventually_mem_image Ψ G hG (ball_mem_nhds 0 hε))

  haveI : ProperSpace (realLie Ψ G) := FiniteDimensional.proper_real _
  obtain ⟨δ₀, hδ₀, hinj⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ InjOn (chartExp Ψ G hG) (closedBall 0 δ₀) := by
    obtain ⟨s, hs, ha⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
    obtain ⟨δ, hδ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hs
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    have h1 := ha x (hsub hx) y (hsub hy)
    simp only [hxy, sub_self, zero_sub, norm_neg, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] at h1
    have h2 : ‖x - y‖ ≤ 0 := by
      have h3 : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
      rw [h3] at h1
      linarith
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  have hK : MeasurableSet (closedBall (0 : realLie Ψ G) δ₀) := measurableSet_closedBall
  have hemb := ContinuousOn.measurableEmbedding hK he.continuousOn hinj
  set ν : Measure (realLie Ψ G) :=
    (μ.comap ((closedBall (0 : realLie Ψ G) δ₀).domRestrict (chartExp Ψ G hG))).map Subtype.val with hν
  have hνS : ∀ S : Set (realLie Ψ G), MeasurableSet S →
      ν S = μ (chartExp Ψ G hG '' (S ∩ closedBall 0 δ₀)) := by
    intro S hS
    rw [hν, Measure.map_apply measurable_subtype_coe hS, hemb.comap_apply]
    congr 1
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hνsub : ∀ S : Set (realLie Ψ G), MeasurableSet S → S ⊆ closedBall 0 δ₀ →
      ν S = μ (chartExp Ψ G hG '' S) := fun S hS h => by rw [hνS S hS, inter_eq_left.2 h]
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνS _ MeasurableSet.univ, univ_inter]
    exact ((isCompact_closedBall _ _).image he).measure_lt_top
  have hball : ∀ (X : realLie Ψ G) (ρ : ℝ), ‖X‖ + ρ ≤ δ₀ → ball X ρ ⊆ closedBall 0 δ₀ := by
    intro X ρ h y hy
    rw [mem_ball_iff_norm] at hy
    rw [mem_closedBall_zero_iff]
    have := norm_le_norm_add_norm_sub' y X
    linarith
  have hpos : ∀ ρ > 0, 0 < ν (closedBall (0 : realLie Ψ G) ρ) := by
    intro ρ hρ
    have h1 : ν (ball 0 (min ρ δ₀)) ≠ 0 := by
      rw [hνsub _ measurableSet_ball (hball 0 _ (by simp))]
      exact (μ.measure_pos_of_mem_nhds (hn _ (lt_min hρ hδ₀))).ne'
    exact pos_iff_ne_zero.2 fun h => h1 (measure_mono_null
      ((ball_subset_closedBall).trans (closedBall_subset_closedBall (min_le_left _ _))) h)

  have himg : ∀ (g : realSU Ψ G) (S : Set (realSU Ψ G)), μ ((fun h => g * h) '' S) = μ S := fun g S => by
    rw [image_mul_left, measure_preimage_mul]
  have hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, Formalism.BasicNotions.Examples₂.CD.QInv ν ε δ := by
    intro ε hε0 hε1
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.translate_chart_ball_distortion _ _ _ (chartExp Ψ G hG) (matR Ψ G) ι
      (fun g => L₀ (matR Ψ G g)) he he0 hd hL hL1 hm hn (1 + ε / 3) (by linarith)
    refine ⟨min (δ / 2) (δ₀ / 4), by positivity, fun X hX ρ hρ0 hρ => ?_⟩
    have hXδ : ‖X‖ < δ / 2 := lt_of_lt_of_le hX (min_le_left _ _)
    have hX4 : ‖X‖ < δ₀ / 4 := lt_of_lt_of_le hX (min_le_right _ _)
    have hρδ : ρ < δ / 2 := lt_of_lt_of_le hρ (min_le_left _ _)
    have hρ4 : ρ < δ₀ / 4 := lt_of_lt_of_le hρ (min_le_right _ _)
    have hXb : X ∈ ball (0 : realLie Ψ G) δ := mem_ball_zero_iff.2 (by linarith)
    have hκ0 : 0 < 1 + ε / 3 := by linarith
    have hκ2 : 1 + ε / 3 < 2 := by linarith
    have hcl0 : closedBall (0 : realLie Ψ G) ρ ⊆ closedBall 0 δ₀ :=
      closedBall_subset_closedBall (by linarith)
    constructor
    · have hr1 : 0 < ρ / (1 + ε / 3) := div_pos hρ0 hκ0
      have hr2 : ρ / (1 + ε / 3) < ρ := div_lt_self hρ0 (by linarith)
      have hr3 : (1 - ε) * ρ < ρ / (1 + ε / 3) := by
        rw [lt_div_iff₀ hκ0]; nlinarith [mul_pos hρ0 hε0, mul_pos (mul_pos hρ0 hε0) hε0]
      have H2 := (H X hXb (ρ / (1 + ε / 3)) ⟨hr1, by linarith⟩).2
      rw [mul_div_cancel₀ _ hκ0.ne'] at H2
      calc ν (closedBall X ((1 - ε) * ρ)) ≤ ν (ball X (ρ / (1 + ε / 3))) :=
            measure_mono (closedBall_subset_ball hr3)
        _ = μ (chartExp Ψ G hG '' ball X (ρ / (1 + ε / 3))) :=
            hνsub _ measurableSet_ball (hball X _ (by linarith))
        _ ≤ μ ((fun h => chartExp Ψ G hG X * h) '' (chartExp Ψ G hG '' ball 0 ρ)) := measure_mono H2
        _ = μ (chartExp Ψ G hG '' ball 0 ρ) := himg _ _
        _ ≤ μ (chartExp Ψ G hG '' closedBall 0 ρ) := measure_mono (image_mono ball_subset_closedBall)
        _ = ν (closedBall 0 ρ) := (hνsub _ measurableSet_closedBall hcl0).symm
    · have hr1 : 0 < (1 + ε / 3) * ρ := by positivity
      have hr2 : (1 + ε / 3) * ρ < δ := by nlinarith
      have H1 := (H X hXb ((1 + ε / 3) * ρ) ⟨hr1, hr2⟩).1
      have hsq : (1 + ε / 3) * ((1 + ε / 3) * ρ) ≤ (1 + ε) * ρ := by
        nlinarith [mul_pos (mul_pos hρ0 hε0) (by linarith : (0:ℝ) < 3 - ε)]
      calc ν (closedBall 0 ρ) ≤ ν (ball 0 ((1 + ε / 3) * ρ)) :=
            measure_mono (closedBall_subset_ball (by nlinarith))
        _ = μ (chartExp Ψ G hG '' ball 0 ((1 + ε / 3) * ρ)) :=
            hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; nlinarith))
        _ = μ ((fun h => chartExp Ψ G hG X * h) '' (chartExp Ψ G hG '' ball 0 ((1 + ε / 3) * ρ))) :=
            (himg _ _).symm
        _ ≤ μ (chartExp Ψ G hG '' ball X ((1 + ε / 3) * ((1 + ε / 3) * ρ))) := measure_mono H1
        _ = ν (ball X ((1 + ε / 3) * ((1 + ε / 3) * ρ))) :=
            (hνsub _ measurableSet_ball (hball X _ (by nlinarith))).symm
        _ ≤ ν (closedBall X ((1 + ε) * ρ)) :=
            measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hsq))
  obtain ⟨c, hc0, hct, hup, hdown⟩ := Formalism.BasicNotions.Examples₂.CD.exists_density lam ν hq hpos

  have hνt : ∀ ε : ℝ, 0 < ε → (lam.map Subtype.val) (tanBall Ψ r ε) = lam (ball 0 ε) := by
    intro ε hε
    rw [Measure.map_apply measurable_subtype_coe, preimage_tanBall Ψ G hε]
    rw [show tanBall Ψ r ε = ball (0 : Ψ → Fin r → Fin r → ℂ) ε by
      ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl]
    exact measurableSet_ball
  have hc : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) < c := by
    by_contra hcon
    rw [not_lt] at hcon
    have h34 : c < ((3 / 4 : ℝ≥0) : ℝ≥0∞) :=
      lt_of_le_of_lt hcon (by rw [ENNReal.coe_lt_coe]; norm_num)
    obtain ⟨δ₁, hδ₁, H1⟩ := hup (3 / 4) h34
    obtain ⟨t, ht1, htn⟩ : ∃ t : ℝ, 1 < t ∧ t ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 := by
      have h := ((continuous_pow (Module.finrank ℝ (realLie Ψ G))).tendsto (1 : ℝ)).eventually
        (gt_mem_nhds (show (1 : ℝ) ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 by norm_num))
      have h' : ∀ᶠ x in 𝓝[>] (1 : ℝ), x ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 :=
        h.filter_mono nhdsWithin_le_nhds
      obtain ⟨t, h1, h2⟩ := (h'.and self_mem_nhdsWithin).exists
      exact ⟨t, h2, h1⟩
    have ht0 : 0 < t := by linarith
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ (grpBall (realSU Ψ G) ε) / (lam.map Subtype.val) (tanBall Ψ r ε) ≤
        ((3 / 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t ^ Module.finrank ℝ (realLie Ψ G)) := by
      filter_upwards [chart_squeeze Ψ G hG ht1,
        Ioo_mem_nhdsGT (show 0 < min δ₁ δ₀ / t by positivity)] with ε hsq hε
      obtain ⟨hε0, hε1⟩ := hε
      have hte : t * ε < min δ₁ δ₀ := by rw [mul_comm]; exact (lt_div_iff₀ ht0).1 hε1
      rw [lt_min_iff] at hte
      rw [hνt ε hε0]
      refine ENNReal.div_le_of_le_mul ?_
      calc μ (grpBall (realSU Ψ G) ε) ≤ μ (chartExp Ψ G hG '' ball 0 (t * ε)) := measure_mono hsq.2
        _ = ν (ball 0 (t * ε)) :=
            (hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; linarith))).symm
        _ ≤ ((3 / 4 : ℝ≥0) : ℝ≥0∞) * lam (ball 0 (t * ε)) := H1 _ (ball_subset_ball hte.1.le)
        _ = _ := by rw [Measure.addHaar_ball_mul_of_pos lam 0 ht0 ε, mul_assoc]
    have h1 := le_of_tendsto hD hev
    have h2 : ((3 / 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t ^ Module.finrank ℝ (realLie Ψ G)) < 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_one]
      push_cast
      linarith
    exact absurd h1 (not_le.2 h2)
  obtain ⟨δ₂, hδ₂, H2⟩ := hdown 2⁻¹ hc
  refine ⟨min δ₂ δ₀, lt_min hδ₂ hδ₀, fun s hs hsub => ?_⟩
  have h1 := H2 s (hsub.trans (ball_subset_ball (min_le_left _ _)))
  have h2 : ν s = μ (chartExp Ψ G hG '' s) :=
    hνsub s hs (hsub.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall))
  rw [← h2]
  have h22 : (2 : ℝ≥0∞) * ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.coe_inv two_ne_zero]
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  calc lam s = 2 * (((2⁻¹ : ℝ≥0) : ℝ≥0∞) * lam s) := by rw [← mul_assoc, h22, one_mul]
    _ ≤ 2 * ν s := by gcongr

end GlobalTheory.CovTop.VolUp.LowDens
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieHaarLeTwoMulTangentNormalizedHaarStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → lam s ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
  first | exact @GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar | exact GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar | (intros; apply GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGeStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.riemannianLieMeasure_frameBox_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ((ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε} := by
  first | exact @GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge | exact GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge | (intros; apply GlobalTheory.CovTop.VolUp.riemLie_frameBox_ge <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLowerBound

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowBall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

theorem exists_conj_bound (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (X : Ψ → Fin r → Fin r → ℂ), 0 ≤ t →
      (∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ ≤ t) → ‖X‖ ≤ C * t := by
  let L : (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        change mat x τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        change mat x τ * ((c : ℂ) • Matrix.of (Y τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖ + 1, by positivity, fun t X ht hX => ?_⟩
  let Y : Ψ → Fin r → Fin r → ℂ := fun τ => ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  have hLY : Lc Y = X := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) * (mat x τ)⁻¹ = Matrix.of (X τ)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hY : ‖Y‖ ≤ t := by
    refine (pi_norm_le_iff_of_nonneg ht).2 fun τ => (pi_norm_le_iff_of_nonneg ht).2 fun a =>
      (pi_norm_le_iff_of_nonneg ht).2 fun b => hX τ a b
  calc ‖X‖ = ‖Lc Y‖ := by rw [hLY]
    _ ≤ ‖Lc‖ * ‖Y‖ := Lc.le_opNorm Y
    _ ≤ ‖Lc‖ * t := by gcongr
    _ ≤ (‖Lc‖ + 1) * t := by nlinarith

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_exp_bound (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < δ → ‖NormedSpace.exp Y - 1‖ ≤ 2 * ‖Y‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (zero_lt_one' ℝ)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero, one_mul] at this
  have this : ‖NormedSpace.exp Y - 1 - Y‖ ≤ ‖Y‖ := this
  calc ‖NormedSpace.exp Y - 1‖ = ‖Y + (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
    _ ≤ ‖Y‖ + ‖NormedSpace.exp Y - 1 - Y‖ := norm_add_le _ _
    _ ≤ 2 * ‖Y‖ := by linarith

theorem exists_exp_entry (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (Y : Matrix n n ℂ), 0 < ε → ε < δ → (∀ a b, ‖Y a b‖ < ε / 2) →
      ∀ a b, ‖(NormedSpace.exp Y - 1) a b‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_exp_bound n
  refine ⟨δ, hδ, fun ε Y hε hεδ hY a b => ?_⟩
  have hYn : ‖Y‖ < ε / 2 := (Matrix.norm_lt_iff (by positivity)).2 hY
  calc ‖(NormedSpace.exp Y - 1) a b‖ ≤ ‖NormedSpace.exp Y - 1‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖Y‖ := h Y (by linarith)
    _ < ε := by linarith

end Exp

theorem riemHaar_frBall_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ENNReal.ofReal ((ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2) ≤
        riemHaar Ψ G x (frBall Ψ G x ε) := by
  intro E _ _ _ r Ψ G x hr hG hx
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hlow⟩ := GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar E r Ψ G hG lam
  obtain ⟨C, hC, hconj⟩ := exists_conj_bound Ψ x hx
  obtain ⟨δ', hδ', hexp⟩ := exists_exp_entry (Fin r)
  refine ⟨min 2 (min δ' (δ / C)), lt_min two_pos (lt_min hδ' (div_pos hδ hC)), fun ε hε hε₀ => ?_⟩
  have hε2 : ε < 2 := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεδ' : ε < δ' := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε < δ / C := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_right _ _))
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε / 2} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := Subtype.val ⁻¹' S with hs
  have hsm : MeasurableSet s := measurable_subtype_coe hSm
  have h1 : ENNReal.ofReal ((ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ lam s := by
    have := GlobalTheory.T.riemannianLieMeasure_frameBox_ge E r Ψ G x hr hG hx (ε / 2) (by positivity) (by linarith)
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm] at this
    exact this
  have hball : s ⊆ Metric.ball 0 δ := by
    intro X hX
    rw [mem_ball_zero_iff]
    have h := hconj (ε / 2) X.1 (by positivity) fun τ a b => (hX τ a b).le
    have hCε : C * ε < δ := by rw [lt_div_iff₀ hC] at hεC; linarith
    calc ‖X‖ = ‖X.1‖ := rfl
      _ ≤ C * (ε / 2) := h
      _ < δ := by nlinarith
  have himg : GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s ⊆ frBall Ψ G x ε := by
    rintro _ ⟨X, hX, rfl⟩ τ a b
    change ‖((mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1) a b‖ < ε
    rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
    exact hexp ε _ hε hεδ' (hX τ) a b
  have h2 := hlow s hsm hball
  have h3 : tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤
      riemHaar Ψ G x (frBall Ψ G x ε) := by
    rw [hmap]; exact measure_mono himg
  have e : ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) = ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) := by rw [div_div]
  rw [e, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  refine ENNReal.div_le_of_le_mul ?_
  calc _ ≤ lam s := h1
    _ ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := h2
    _ ≤ 2 * riemHaar Ψ G x (frBall Ψ G x ε) := by gcongr
    _ = riemHaar Ψ G x (frBall Ψ G x ε) * 2 := mul_comm _ _

end GlobalTheory.CovTop.VolUp.LowBall
end
end
end
