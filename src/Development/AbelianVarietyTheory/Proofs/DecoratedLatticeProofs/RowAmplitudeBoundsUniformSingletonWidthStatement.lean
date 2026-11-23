module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsAllAtRecordGap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ElementarySizeBoundsOfSizeHypotheses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeBoundsAtParametersOfAdmittedBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThresholdCriticalLevelLowerBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqKFiniteOrbitalIntegralGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGaps
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGap
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurAtRecordGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqVandermondeRatioAlongLineStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFormalDegreeEqVandermondeOfSizesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdSubEqProdFactorial

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpleThetaWideRangeLargeConstants

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem ptWide_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hDB : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  have hBp : BpJoin.ThmBpDS := GlobalTheory.discreteSeriesCoef_pointwiseBound
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp hDB
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Cb, Cg₀, hB⟩ := GlobalTheory.bp_forms_of_gapIn_thmBpDS hDB hBp 1
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.AmpBesselGap.ampIsBessel hDB Cg cb Cu cT CT C0 1
  refine ⟨max (Ca + max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0),
    fun Cn => ?_⟩
  obtain ⟨m₀, hm₀⟩ := hAmp Cn
  obtain ⟨Cs₀, hCs₀⟩ := hFrm Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ (max (128 * |max Cg₀ Cs₀|) (200 * |Cn|)))
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hTies hTF => ?_⟩
  intro hH
  obtain ⟨h1000, -, hM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH.1
  have hβ2 : (2 : ℝ) ≤ max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hStd : Bridge.StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|)
      (max (max 2 Cu) (max CT (1 / 8 + 2 * Cg))) :=
    stdOfHyp_rec D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|) _ (by linarith) zero_le_one hβ2
      (le_trans (le_max_right _ _) (le_max_left _ _))
      (by rw [mul_one]; exact le_trans (le_max_left _ _) (le_max_right _ _))
      (by rw [mul_one]; exact le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM)
      (by
        rw [abs_of_nonneg (by positivity)]
        exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM)
  have h47 : OnePlaceEstimates.UniformityTheoremBPrime D 1 Cn (max Cg₀ Cs₀) (200 * |Cn|) (max Cb 0) :=
    OnePlaceEstimates.upper_bound_mono_constant D zero_lt_one (le_max_left _ _)
      ((hB (max Cg₀ Cs₀) (le_max_left _ _)).2.2 D Cn (200 * |Cn|)
        (mul_le_mul_of_nonneg_left (le_abs_self Cn) (by norm_num)))
  have hFr : Bridge.FrameChange D 1 (max Cg₀ Cs₀) Cn Cf :=
    hCs₀ (max Cg₀ Cs₀) (le_max_right _ _) D (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D))
  exact AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 Ca 1 Cf (max Cg₀ Cs₀) (200 * |Cn|) _ (max Cb 0) _
    (hm₀ D large₂ C' Cl h1000 hrd (le_trans (le_max_left _ _) hM) hTies.cdScale_tie) hFr hStd (fun _ => hTF) h47
    (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _) hH

end GlobalTheory.Core.Deg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpleThetaWideRangeLargeConstantsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.ampleTheta_wideRange_large_constants : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  first | exact @GlobalTheory.Core.Deg.ptWide_at_record_gap | exact GlobalTheory.Core.Deg.ptWide_at_record_gap | (intros; apply GlobalTheory.Core.Deg.ptWide_at_record_gap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtDlAtRecord

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreDlGap

theorem ptDl_at_record : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨C, hC⟩ :=
    GlobalTheory.CellMinorLineGap.minor_line hH (GlobalTheory.AmpOrbGap.ampKF hH) GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 1
  refine ⟨C, fun Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ 1)
  refine ⟨thr, fun D large₂ C' Cl h1 h2 hT => ?_⟩
  intro hH0
  obtain ⟨hCl, -, hMm, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT h1 h2 hH0.1
  have hmm : m₀ ≤ (D.R.m : ℝ) := (le_max_left _ _).trans hMm
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := (le_max_right _ _).trans hMm
  have hbig : GlobalTheory.Amp.Big D large₂ Cl m₀ := ⟨hrd, by nlinarith, hmm⟩
  exact hm D large₂ C' Cl hCl hbig hT.cdScale_tie hH0

end GlobalTheory.CoreDlGap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealPlaceAmplitudeNormLeConstDivFormalDegree

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.BridgeLemma

namespace GlobalTheory.AmpRec

theorem exists_threshold_adm9_of_ties : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ),
    thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 := by
  intro Cg cb Cu cT CT C0 Cn
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨m₀, hm⟩ := GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap hH (GlobalTheory.AmpOrbGap.ampKF hH)
    GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 1 Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ 1)
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hT => ?_⟩
  intro hH0
  obtain ⟨h1000, -, hmM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hmm : m₀ ≤ (D.R.m : ℝ) := (le_max_left _ _).trans hmM
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := (le_max_right _ _).trans hmM
  have hbig : GlobalTheory.Amp.Big D large₂ Cl m₀ := ⟨hrd, by nlinarith, hmm⟩
  exact hm D large₂ C' Cl h1000 hbig hT.cdScale_tie hH0

end GlobalTheory.AmpRec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealPlaceAmplitudeNormLeConstDivFormalDegreeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPlaceAmplitude_norm_le_const_div_formalDegree : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 := by
  first | exact @GlobalTheory.AmpRec.exists_threshold_adm9_of_ties | exact GlobalTheory.AmpRec.exists_threshold_adm9_of_ties | (intros; apply GlobalTheory.AmpRec.exists_threshold_adm9_of_ties <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowColumnShapeOfWindowDataWidthGeOneStatement

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dataNW_of_standingNumericalData : ∀ (D : D7) (C0 : ℝ), 1 ≤ C0 → StandingNumericalData D C0 → DataNW D := by
  first | exact @GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one | exact GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one | (intros; apply GlobalTheory.Core.Deg.rowColumnShape_of_windowData_width_ge_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidth

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpRecordGap

theorem isHCParam_u (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  have hk := R.m_add_three_le_k
  obtain ⟨c, hc⟩ := R.k_even
  have step : ∀ (i : ℕ) (h : i + 1 < R.k), P.u ⟨i + 1, h⟩ < P.u ⟨i, by omega⟩ := fun i h =>
    lt_trans (P.v_gt_u ⟨i, by omega⟩) (P.u_gt_v ⟨i, by omega⟩)
  refine ⟨?_, fun a => ?_⟩
  · have key : ∀ (d i : ℕ) (h : i + d + 1 < R.k), P.u ⟨i + d + 1, h⟩ < P.u ⟨i, by omega⟩ := by
      intro d
      induction d with
      | zero => intro i h; exact step i h
      | succ d ih => intro i h; exact lt_trans (step (i + d + 1) h) (ih i (by omega))
    intro i j hij
    have hlt : i.val < j.val := hij
    have := key (j.val - i.val - 1) i.val (by omega)
    have e : P.u ⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ = P.u j := congrArg P.u (Fin.ext (by simp; omega))
    rw [e] at this
    beta_reduce
    exact_mod_cast this
  · obtain ⟨z, hz⟩ := P.u_half a
    refine ⟨z - c + 1, ?_⟩
    simp only
    rw [hz, hc]; push_cast; ring

theorem isHCParam_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (uS D w τ) :=
  isHCParam_u D.R (D.hcW w τ)

theorem weyl_at (D : D7) : VanishingOnXAndXPlusBranching.adm12 D := by
  intro τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D w τ)).1 H _ hg

theorem ampOn_singleton : ∀ c : ℝ, AmpOn {c} := by
  intro c Cg cb Cu cT CT hcb _
  obtain ⟨CPT, hPT⟩ := GlobalTheory.T.ampleTheta_wideRange_large_constants Cg cb Cu cT CT c
  obtain ⟨CDl, hDl⟩ := GlobalTheory.CoreDlGap.ptDl_at_record Cg cb Cu cT CT c
  obtain ⟨Ca, hCa, hAbs⟩ := GlobalTheory.AbsRecGap.abs_all_at_record_gap Cg cb Cu cT CT c
  obtain ⟨CS, tS, hS⟩ := GlobalTheory.Amp.schur_at_record_gap Cg cb Cu cT CT c
  obtain ⟨tL, hL⟩ := GlobalTheory.T.exists_threshold_criticalLevel_lower_bound cb Cu hcb
  obtain ⟨tV, hV⟩ := GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.T.ampAt_of_admitted_bounds Cg CPT CDl 1 Ca CS zero_le_one hCa
  refine ⟨C, C2, Ch, hC, hCh, fun Cpr δ hδ => ?_⟩
  obtain ⟨t0, H0⟩ := H Cpr δ hδ
  obtain ⟨t1, h1⟩ := hPT (max Cpr 0)
  obtain ⟨t2, h2⟩ := hDl (max Cpr 0)
  obtain ⟨t3, h3⟩ := GlobalTheory.T.realPlaceAmplitude_norm_le_const_div_formalDegree Cg cb Cu cT CT c (max Cpr 0)
  obtain ⟨t4, h4⟩ := hAbs (max Cpr 0)
  obtain ⟨t5, h5⟩ := GlobalTheory.T.formalDegree_ratio_eq_vandermonde_ratio_along_line (max Cpr 0)
  refine ⟨max t0 (max t1 (max t2 (max t3 (max t4 (max tS (max tL (max tV t5))))))),
    fun C0 hC0 C' Cl hC' hCl D large₂ hG hT _ hTF => ?_⟩
  obtain rfl : C0 = c := hC0
  simp only [max_le_iff] at hC' hCl
  obtain ⟨a0, a1, a2, a3, a4, aS, -, aV, a5⟩ := hC'
  obtain ⟨b0, b1, b2, b3, b4, bS, bL, bV, b5⟩ := hCl
  have hLow : VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 := fun h0 =>
    hL D large₂ C' Cl Cg cT CT C0 bL
      (hV D large₂ C' Cl Cg cb Cu cT CT aV bV hT h0.1 (GlobalTheory.T.dataNW_of_standingNumericalData D C0 h0.2.2 h0.2.1)) h0
  exact H0 D large₂ C' Cl cb Cu cT CT C0 a0 b0 hG
    (h1 D large₂ C' Cl a1 b1 hT hTF)
    (h2 D large₂ C' Cl a2 b2 hT)
    hLow
    (h3 D large₂ C' Cl a3 b3 hT)
    (Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
      (h5 D large₂ C' Cl Cg cb Cu cT CT C0 1 a5 b5 hT))
    (h4 D large₂ C' Cl a4 b4)
    (hS D large₂ C' Cl aS bS hT)
    (weyl_at D)

end GlobalTheory.AmpRecordGap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width : ∀ c : ℝ, AmpOn {c} := by
  first | exact @GlobalTheory.AmpRecordGap.ampOn_singleton | exact GlobalTheory.AmpRecordGap.ampOn_singleton | (intros; apply GlobalTheory.AmpRecordGap.ampOn_singleton <;> assumption)
end
end
