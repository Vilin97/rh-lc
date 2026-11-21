module

public import Mathlib
public import Formalism.LocalToGlobal.ThresholdSelection
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowsOfLargeGapDiscreteSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBesselStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditionalStatement
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksOfRecord
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverOfNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeEqMassOfReal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevelStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TFrameOfRanksRowThree
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClass

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn
namespace GlobalTheory.LoopRowsByName
theorem loopRows_of_rowsFinDim_alt :
    Formalism.L2.SG.RowsDef.RowsFinDim → (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
      ∀ sel : SSel 𝒞, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → LoopRowS 3 𝒞 sel := by
  intro hFin hUT 𝒞 hT sel hTu
  exact GlobalTheory.T.loopRows_of_large_gap_discreteSeries (GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.1) GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.2 GlobalTheory.T.discreteSeriesCoef_pointwiseBound_unconditional
    GlobalTheory.wuDecayOfGap hFin 𝒞 sel hTu (_root_.GlobalTheory.ranks_and_frame_of_tied_class_alt hUT 𝒞 hT).1
end GlobalTheory.LoopRowsByName
end
