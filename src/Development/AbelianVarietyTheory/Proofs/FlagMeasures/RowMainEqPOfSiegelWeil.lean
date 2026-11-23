module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedSteps
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChainStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DifferentLocalIdentityFamiliesLemmaHStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProofStatement
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeaves
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericScalarClassTermsFormFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalMassLeGenericMassConstNine
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqNml
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlIntHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlLineHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepChoiceConstantsCOfSiegelWeilAtInfinity

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedStepsStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.equalWordGenericBound_of_normalisedSteps : PN.NGChain → StepClassG → StepNormalsG → StepPointsG → StepNormOneG → TieOfCtx → StepChoiceConstantsC → StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → GlobalTheory.SnPos.RowMainEqP := by
  first | exact @GlobalTheory.SnPos.rowMainEqP_of_pinned | exact GlobalTheory.SnPos.rowMainEqP_of_pinned | (intros; apply GlobalTheory.SnPos.rowMainEqP_of_pinned <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericRowFamilyStepOfLeavesStatement

section

@[expose] public section

open GlobalTheory.SnFam

theorem _root_.GlobalTheory.T.genericRow_familyStep_of_leaves : (∀ D : Formalism.BasicNotions.D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) → Formalism.L2.SG.FamDefs.HTie → FamGen → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFam.Gen.stepFamG_of_fam | exact GlobalTheory.SnFam.Gen.stepFamG_of_fam | (intros; apply GlobalTheory.SnFam.Gen.stepFamG_of_fam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericScalarClassTermsFormFamilyStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.genericScalarClassTerms_formFamily : GlobalTheory.SnFam.FamGen := by
  first | exact @GlobalTheory.SnFamGenAll.famGen | exact GlobalTheory.SnFamGenAll.famGen | (intros; apply GlobalTheory.SnFamGenAll.famGen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeil

section

@[expose] public section

open GlobalTheory.SnFam

namespace GlobalTheory.SnFamTop

theorem stepFamG_of_SWXS (hSW : PI.VolStabS.MassDataS.SWXS) :
    Formalism.L2.SG.Pf.MainEqFam.StepFamG :=
  GlobalTheory.T.genericRow_familyStep_of_leaves
    (fun D h => GlobalTheory.localMass_le_genericMass_nine _ _ h)
    GlobalTheory.T.differentLocalIdentity_familiesLemmaH GlobalTheory.T.genericScalarClassTerms_formFamily GlobalTheory.T.familyRowWeightSumUnfoldingIdentity (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW) GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof GlobalTheory.T.familyLocalObjectsExistAtTerms_proof

end GlobalTheory.SnFamTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericFamilyStepOfSiegelWeilStatement

section

@[expose] public section

open GlobalTheory.SnFam

theorem _root_.GlobalTheory.T.genericFamilyStep_of_siegelWeil : PI.VolStabS.MassDataS.SWXS → Formalism.L2.SG.Pf.MainEqFam.StepFamG := by
  first | exact @GlobalTheory.SnFamTop.stepFamG_of_SWXS | exact GlobalTheory.SnFamTop.stepFamG_of_SWXS | (intros; apply GlobalTheory.SnFamTop.stepFamG_of_SWXS <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalCountGenericRow

section

@[expose] public section

open Formalism.L2.SG.Pf.MainEqSteps

namespace GlobalTheory

theorem stepNormalsG_holds : StepNormalsG :=
  Formalism.L2.SG.NGCut.NormalInvariants.Gen.stepNormalsG_of
    (Formalism.L2.SG.Pf.nmlInvG_of Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds
      Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds)
    Formalism.L2.SG.NGCut.NormalCount.NormCount_holds
    GlobalTheory.T.equalWords_nonGeneric_estimates_chain.2.2.2.1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalCountGenericRowStatement

section

@[expose] public section

open Formalism.L2.SG.Pf.MainEqSteps

theorem _root_.GlobalTheory.T.normalCount_genericRow : StepNormalsG := by
  first | exact @GlobalTheory.stepNormalsG_holds | exact GlobalTheory.stepNormalsG_holds | (intros; apply GlobalTheory.stepNormalsG_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeilConstants

section

@[expose] public section

namespace GlobalTheory

theorem rowMainEqP_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.Pf.BDat.StepThmBG → Formalism.L2.SG.RowsPos.RowMainEqP := by
  intro h hB hT
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, _h8, h9⟩ := GlobalTheory.T.equalWords_nonGeneric_estimates_chain
  refine GlobalTheory.T.equalWordGenericBound_of_normalisedSteps h1 h2 GlobalTheory.T.normalCount_genericRow h3 h4 h5 hB h6 h7 (h9 (GlobalTheory.T.genericFamilyStep_of_siegelWeil (GlobalTheory.St.swxs_of_siegelWeil h))) ?_
  intro Cg cb Cw cT CT C0 _ _ A
  obtain ⟨CB, h0, a, b, H⟩ := hT Cg cb Cw cT CT C0 A
  exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u _ => H C' Cl h1 h2 D large₂ X Y u⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeil

section

@[expose] public section

namespace GlobalTheory

theorem rowMainEqP_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsPos.RowMainEqP :=
  fun h => GlobalTheory.rowMainEqP_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h
      (fun _ X u u' hg => Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz
        CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.bDat_theoremB_global

end GlobalTheory
end
end
