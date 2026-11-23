module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CriticalLevelLowOfRefined
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.StandardHypothesesOfScaleHyp
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceExpansion
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGapsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.amplitude_eq_besselFunction_largeGaps : GlobalTheory.GapIn.Hyp → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → D.host.rdE ≤ large₂.sc.b → m₀ ≤ D.R.m → cdScaleTie D → Bridge.AmpIsBessel D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Ca := by
  first | exact @GlobalTheory.AmpBesselGap.ampIsBessel | exact GlobalTheory.AmpBesselGap.ampIsBessel | (intros; apply GlobalTheory.AmpBesselGap.ampIsBessel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGapsStatement

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

theorem _root_.GlobalTheory.T.besselPointwiseBound_at_largeGaps : GlobalTheory.GapIn.Hyp → ThmBpDS → ∀ Ch : ℝ, ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → (∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), LocOk D Ch Cg L lam0 ka b 1 → AllGaps lam0 (200 * l1 L.lam lam0) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec → ∀ γ : Point ℂ (D.R.rS + 1), Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → BpIneq D Cb L f μsec b γ) ∧ (∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.TheoremBPrimePointwise D Ch Cg Cb) ∧ ∀ (D : D7) (Cu Cg' : ℝ), 200 * Cu ≤ Cg' → Formalism.MainNotions.OnePlaceEstimates.UniformityTheoremBPrime D Ch Cu Cg Cg' Cb := by
  first | exact @GlobalTheory.bp_forms_of_gapIn_thmBpDS | exact GlobalTheory.bp_forms_of_gapIn_thmBpDS | (intros; apply GlobalTheory.bp_forms_of_gapIn_thmBpDS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGapStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.oneBessel_torusTranslates_largeGap : GlobalTheory.GapIn.Hyp → ∃ Cgf : ℝ, ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf := by
  first | exact @GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | exact GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | (intros; apply GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGap

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

open MeasureTheory NumberField Formalism.FourierDecayAlt Finset

namespace GlobalTheory.UnifPTGap

open Formalism.MainNotions.BridgeLemma

theorem tFrame_of_dsig (hM : Formalism.HermitianLatticesTheory.SiegelMassRatio) (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC)
    {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 := by
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  exact level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith)
    (level_formula_family Fm C0 Cg cb Cu cT CT (fun x i => mass_ratio_of_siegel_cm_unramified hM (Fm.D x i)) (mass_two_bound_family_holds Fm) hR)
    (Formalism.L2.SG.Pf.SzHypFam.localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

theorem uniformPT_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps),
    thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i =>
      VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  intro hM hH hBp Cg cb Cu cT CT C0 C1
  set Cβ : ℝ := max 2 (max Cu (max CT (1 / 8 + 2 * Cg))) with hCβ
  have hβ2 : 2 ≤ Cβ := le_max_left _ _
  have hu : Cu ≤ Cβ := (le_max_left _ _).trans (le_max_right _ _)
  have hT : CT ≤ Cβ * 1 := by rw [mul_one]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hg : 1 / 8 + 2 * Cg ≤ Cβ * 1 := by
    rw [mul_one]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨Cb, Cg₀, hBP⟩ := (GlobalTheory.T.besselPointwiseBound_at_largeGaps hH hBp 1).imp fun _ h => h.imp fun _ h Cg hCg => (h Cg hCg).2.2
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.T.oneBessel_torusTranslates_largeGap hH
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.T.amplitude_eq_besselFunction_largeGaps hH Cg cb Cu cT CT C0 C1
  refine ⟨max (Ca + Cβ * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0), 1000, fun eps Fm _ hl hR Cn => ?_⟩
  obtain ⟨m₀, hA⟩ := hAmp Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  have hAmpF : OwnEv Fm fun C' Cl x i => Bridge.AmpIsBessel (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Ca :=
    ⟨x0, fun x hx i => hA (Fm.D x i) (Fm.L x i) _ _ hl (hx0 x hx i).2.2.2.2.1 (hx0 x hx i).2.1
      (Fm.ties x i).cdScale_tie⟩
  obtain ⟨a', hFr⟩ := hFrm Cn
  have hStd := Formalism.MainNotions.BridgeLemma.stdHypS_of Fm Cg cb Cu cT CT C0 1 Cβ (by linarith) zero_le_one hβ2 hu hT hg
    (max Cg₀ a') (200 * Cn)
  have hTF := tFrame_of_dsig hM hH.2.2.2 Fm (by linarith) hR
  exact Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H =>
    AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity _ _ _ _ _ _ _ _ _ _ Cn C1 Ca 1 Cf (max Cg₀ a') (200 * Cn) Cβ (max Cb 0) _ H.1.1
      (hFr _ (le_max_right _ _) _ (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus _ Cgf 2 le_rfl (hOB _)))
      H.1.2 H.2
      (OnePlaceEstimates.upper_bound_mono_constant _ one_pos (le_max_left _ _) (hBP _ (le_max_left _ _) _ Cn (200 * Cn) le_rfl))
      (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _)) ((hAmpF.and hStd).and hTF)

end GlobalTheory.UnifPTGap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGapStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  first | exact @GlobalTheory.UnifPTGap.uniformPT_gap | exact GlobalTheory.UnifPTGap.uniformPT_gap | (intros; apply GlobalTheory.UnifPTGap.uniformPT_gap <;> assumption)
end
end
