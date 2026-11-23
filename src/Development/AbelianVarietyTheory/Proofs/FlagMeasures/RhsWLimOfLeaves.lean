module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWbB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.GaugeExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushLoc
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryGroupWbDensityChartStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormula
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasureOrbitRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidInvariantMeasurePolarFormStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVolMt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptoticStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupGaugeVolumeInHermitianUnitary
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ChartLim
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Function.Jacobian
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstPair
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarDec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarHyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsTest
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushM
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PhiDiff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.TBallMeas

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.HyperboloidChartMeasureFormulaStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.hyperboloid_chart_measure_formula : PI.RhsWLim.W.HypChart := by
  first | exact @GlobalTheory.HypChartPf.hypChart | exact GlobalTheory.HypChartPf.hypChart | (intros; apply GlobalTheory.HypChartPf.hypChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasure

section

@[expose] public section

noncomputable section

namespace GlobalTheory.GaugeKExists

theorem gaugeK : PI.RhsWLim.W.GaugeK := by
  intro k r _
  exact ⟨Formalism.L2.SG.Pf.GV.nu0 k r, Formalism.L2.SG.Pf.GV.gauge_measure_is_gauge⟩

end GlobalTheory.GaugeKExists
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserUnitaryGroupHasGaugeMeasureStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure : PI.RhsWLim.W.GaugeK := by
  first | exact @GlobalTheory.GaugeKExists.gaugeK | exact GlobalTheory.GaugeKExists.gaugeK | (intros; apply GlobalTheory.GaugeKExists.gaugeK <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupGaugeVolumeInHermitianUnitaryStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.unitaryGroup_gaugeVolume_in_hermitianUnitary : PI.RhsWLim.W.GaugeVolUk := by
  first | exact @GlobalTheory.GaugeVolFixer.gaugeVolUk | exact GlobalTheory.GaugeVolFixer.gaugeVolUk | (intros; apply GlobalTheory.GaugeVolFixer.gaugeVolUk <;> assumption)
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ChartJac

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace PI.RhsWLim.W

theorem chartJac : ChartJac := by
  intro E _ _ _ _ _ _ Φ ν δ hΦ hdet hδ hδtop hU
  obtain ⟨U, hU, hνU⟩ := hU
  have hstrict : HasStrictFDerivAt Φ
      ((ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero (fderiv ℝ Φ 0) hdet : E ≃L[ℝ] E) :
        E →L[ℝ] E) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hΦ.hasStrictFDerivAt_fderiv (by norm_num)
  have hsrc : (hstrict.toOpenPartialHomeomorph Φ).source ∈ 𝓝 (0 : E) :=
    (hstrict.toOpenPartialHomeomorph Φ).open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source
  have hev : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 1 Φ y := hΦ.eventually (by simp)
  have hUpre : Φ ⁻¹' U ∈ 𝓝 (0 : E) := hΦ.continuousAt.preimage_mem_nhds hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hsrc hev) hUpre)
  have hcont : ContinuousAt (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x)) 0 := by
    have hA : ContinuousAt (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det|) 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp (continuous_abs.continuousAt.comp
        (ContinuousLinearMap.continuous_det.continuousAt.comp (hΦ.continuousAt_fderiv (by norm_num))))
    have hB : ContinuousAt (fun x => δ (Φ x)) 0 := hδ.comp hΦ.continuousAt
    exact ENNReal.Tendsto.mul hA (Or.inr hδtop) hB (Or.inr ENNReal.ofReal_ne_top)
  have hntop : ENNReal.ofReal |(fderiv ℝ Φ 0).det| * δ (Φ 0) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hδtop
  have heq : ∀ ρ : ℝ, 0 < ρ → ρ < ε → ν (Φ '' Metric.ball 0 ρ) =
      ∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x) := by
    intro ρ _ hρε
    have hsub : Metric.ball (0 : E) ρ ⊆ Metric.ball 0 ε := Metric.ball_subset_ball hρε.le
    have hinj : Set.InjOn Φ (Metric.ball 0 ρ) := by
      rw [← hstrict.toOpenPartialHomeomorph_coe]
      exact (hstrict.toOpenPartialHomeomorph Φ).injOn.mono fun x hx => (hball (hsub hx)).1.1
    have hcd : ∀ x ∈ Metric.ball (0 : E) ρ, ContDiffAt ℝ 1 Φ x := fun x hx => (hball (hsub hx)).1.2
    have hdiff : ∀ x ∈ Metric.ball (0 : E) ρ,
        HasFDerivWithinAt Φ (fderiv ℝ Φ x) (Metric.ball 0 ρ) x := fun x hx =>
      ((hcd x hx).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    have hcon : ContinuousOn Φ (Metric.ball 0 ρ) := fun x hx =>
      (hcd x hx).continuousAt.continuousWithinAt
    have hmeas : MeasurableSet (Φ '' Metric.ball 0 ρ) :=
      Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hcon hinj
    have himg : Φ '' Metric.ball 0 ρ ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hball (hsub hx)).2
    rw [hνU _ himg hmeas]
    exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      Metric.isOpen_ball.measurableSet hdiff hinj δ
  have hlim := chartLim E E Φ ν (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x)) hcont hntop
    ⟨ε, hε, heq⟩
  have h0 : (ENNReal.ofReal |(fderiv ℝ Φ 0).det| * δ (Φ 0)).toReal =
      (δ (Φ 0)).toReal * |(fderiv ℝ Φ 0).det| := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), mul_comm]
  rw [← h0]
  exact hlim

end PI.RhsWLim.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ConstTop

section

@[expose] public section

noncomputable section

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem constVal_of_unimodW_orbitPush (hU : UnimodW) (hO : OrbitPush) : ConstVal :=
  constVal_of_polarHyp rhsTest transW hU hO polarHyp

theorem constVal_of_orbit (hO : OrbitPush) : ConstVal :=
  constVal_of_unimodW_orbitPush unimodW hO

end PI.RhsWLim.W
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWLimOf

section

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem rhsWLim_of (hM : MBaseMem) (hB : TBallMeas) (hG : GaugeExists) (hR : RhsHaar) (hU : HaarUniq)
    (hC : ConstVal) : RhsWLim := by
  intro k r z z' μW μW' a a' μsec hD
  have hk := hD.k_pos
  obtain ⟨νg, hνg, ⟨ε, hε, hpos⟩, hlim⟩ := hG k r hk
  obtain ⟨ν, hν, ⟨ε', hε', hfin⟩, hrep⟩ := hR k r z z' μW μW' a a' μsec hD
  obtain ⟨c, hc, hνc⟩ := hU k r ν νg hk hν hνg ⟨min ε ε', lt_min hε hε', fun ρ h0 hlt =>
    ⟨hfin ρ h0 (lt_of_lt_of_le hlt (min_le_right _ _)),
     (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).1,
     (hpos ρ h0 (lt_of_lt_of_le hlt (min_le_left _ _))).2⟩⟩
  have hrep' : ∀ φ : Mt k r → ℝ≥0∞, Measurable φ →
      rhsW k r z z' μW μW' μsec φ = c * ∫⁻ x, φ x ∂νg := by
    intro φ hφ
    rw [hrep φ hφ, hνc, lintegral_smul_measure, smul_eq_mul]
  have hcv := hC k r z z' μW μW' a a' μsec hD νg c hνg hlim hrep'
  have hm := hM k r z z' μW μW' a a' μsec hD
  have hmeas : ∀ ρ, MeasurableSet (mBall k r z z' μsec ρ) := fun ρ => hB k r (mBase k r z z' μsec) ρ
  have heq : ∀ ρ, (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ
      = c.toReal * ((νg (tBall k r (mBase k r z z' μsec) ρ)).toReal / bVol k r ρ) := by
    intro ρ
    rw [hrep' _ (measurable_one.indicator (hmeas ρ)), lintegral_indicator_one (hmeas ρ),
      ENNReal.toReal_mul, mul_div_assoc]
    all_goals rfl
  refine (tendsto_congr heq).2 ?_
  rw [← hcv]
  have := (hlim _ hm).const_mul c.toReal
  rw [mul_one] at this
  exact this

end PI.RhsWLim.W
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RhsWLimOfLeaves

section

@[expose] public section

noncomputable section

namespace GlobalTheory.RankOneChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.RI

theorem rhsWLim_of_leaves (hD : HaarDens) (hQ : HypQ) (hC : HypChart) (hK : GaugeK) (hV : GaugeVolUk)
    (hT : TubeLimK) (hR : OrbRepY) : Formalism.L2.SG.Pf.WB.RhsWLim := by
  have hL : PI.RhsWLim.RhsWLim :=
    rhsWLim_of mBaseMem tBallMeas (gaugeExists_of_dens hD) (rhsHaar_of (rhsWInv_of_hypQ hQ)) haarUniq
      (constVal_of_orbit (orbitPush_of hV hK hT (hypInv_of lebInvB (coneForm_of hypTh coneVol)) hR
        (hypLocal_of chartJac hC hermitianDefectAdd) opEMeas hypLF))
  exact fun k r z z' μW μW' a a' μsec hW => hL k r z z' μW μW' a a' μsec
    ⟨hW.k_pos, hW.z_mem, hW.z'_mem, hW.T_pos, hW.T'_pos, hW.haarW, hW.haarW', hW.a_pos, hW.a'_pos, hW.massW,
      hW.massW', hW.sec⟩

theorem rhsWLim : Formalism.L2.SG.Pf.WB.RhsWLim :=
  rhsWLim_of_leaves GlobalTheory.T.haar_unitaryGroupWb_density_chart GlobalTheory.T.hyperboloid_invariant_measure_polar_form GlobalTheory.T.hyperboloid_chart_measure_formula GlobalTheory.T.stabiliser_unitaryGroup_has_gaugeMeasure GlobalTheory.T.unitaryGroup_gaugeVolume_in_hermitianUnitary GlobalTheory.T.stabilizerTube_gaugeMass_asymptotic GlobalTheory.T.hyperboloid_invariant_measure_orbit_representation

instance : Fact (Formalism.L2.SG.Pf.WB.RhsWLim) := ⟨rhsWLim⟩

end GlobalTheory.RankOneChart
end
end
end
