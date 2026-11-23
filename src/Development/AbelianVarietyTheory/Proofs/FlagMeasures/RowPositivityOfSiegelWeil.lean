module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremi
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProofStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOneTermsFamilyCutByDefectStatement
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepChoiceConstantsCOfSiegelWeilAtInfinity

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremiStatement

section

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem _root_.GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises : StepChoiceConstantsC → StepPinExists → Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric → Formalism.L2.SG.FamDefs.WeightsNG → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric → Formalism.L2.SG.FamDefs.ExistNG → RowNGP := by
  first | exact @GlobalTheory.rowNGP_of_leaves | exact GlobalTheory.rowNGP_of_leaves | (intros; apply GlobalTheory.rowNGP_of_leaves <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatements

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SnFamNG

theorem ampQ_id {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ id L = L.ampNG := by
  funext d
  unfold ampQ PN.LocalNG.ampNG
  simp only [id]

theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}
    {νL νB : X.B.I.Ginf → Measure X.B.I.Ginf} {ng : PN.Pts D.host.E D.R.rS → ℝ} {γ : PN.Pts D.host.E D.R.rS}
    (h : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ) : HasPt Y u u' (Y.tO u u').ngSet γ := by
  obtain ⟨-, -, t, ht, hv, -, hp, -⟩ := h
  exact ⟨t, ht, hv, hp⟩

theorem leaves_of_fam : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧
    (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  intro hF
  refine ⟨fun hG => ?_, fun hW => ?_, fun hG4 => ?_, fun hE => ?_⟩
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hG Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S Fm hT => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ
      (hasPt_of_isPt hγ) Fm hT
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hW Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire
      hbk νL νB ng γ hγ S Fm hT hRel hTerm hG5 => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q
      i0 i0' νq Irat Ire hbk _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT hRel hTerm hG5
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨CSt, hCSt, a2, b2, h2⟩ := hG4 Cg cb Cw cT CT C0
    refine ⟨CSt, hCSt, max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc hb X0 ψ hbt sd C Th F0 what₂ vR Q i0 i0'
      νq Irat Ire hbk ν hν => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc hb X0
      ψ hbt sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hbk ν hν
    refine ⟨s, hs1, hs2, hs3, fun γ hγ S Fm hT x _ => ?_⟩
    have h := hs4 _ id _ _ hQ γ (hasPt_of_isPt hγ) Fm hT x.1 x.2
    rw [ampQ_id] at h
    exact h
  · intro Cg cb Cw cT CT C0
    obtain ⟨a1, b1, h1⟩ := hF Cg cb Cw cT CT C0
    obtain ⟨a2, b2, h2⟩ := hE Cg cb Cw cT CT C0
    refine ⟨max a1 a2, max b1 b2, fun C' Cl hC hL D large₂ X Y u u' hc νL νB ng γ hγ S => ?_⟩
    have hQ := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hL) D large₂ X Y u u' hc
    exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hL) D large₂ X Y u u' hc _ id _ _ hQ γ (hasPt_of_isPt hγ)

end GlobalTheory.SnFamNG
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NongenericRowStatementsOfFamilyStatementsStatement

section

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.nongeneric_row_statements_of_family_statements : FamNG → (FamilyWeightSumUnfoldingIdentity → Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) ∧ (WeightsFam → Formalism.L2.SG.FamDefs.WeightsNG) ∧ (FamilyGroupSumFactorsWeightAmplitude → Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) ∧ (ExistFam → Formalism.L2.SG.FamDefs.ExistNG) := by
  first | exact @GlobalTheory.SnFamNG.leaves_of_fam | exact GlobalTheory.SnFamNG.leaves_of_fam | (intros; apply GlobalTheory.SnFamNG.leaves_of_fam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneNonGenericRowBoundClosed

section

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRowClose

theorem rowNGP_of_formNGVanish (hSW : PI.VolStabS.MassDataS.SWXS) (hC : StepChoiceConstantsC)
    (hP : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC) (hB : StepThmBPinnedP) :
    RowNGP := by
  obtain ⟨h5, hw, h4, he⟩ := GlobalTheory.T.nongeneric_row_statements_of_family_statements GlobalTheory.T.non_generic_corank_one_terms_family_cut_by_defect
  exact GlobalTheory.T.corankOnePairsNonGenericRowBound_of_remaining_premises hC hP hF hB (h5 GlobalTheory.T.familyRowWeightSumUnfoldingIdentity) (hw (GlobalTheory.T.familyGenericMassPositiveBounded_proof hSW))
    (h4 GlobalTheory.T.familyGroupSumFactorsRowWeightAmplitude_proof) (he GlobalTheory.T.familyLocalObjectsExistAtTerms_proof)

theorem close : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists →
    Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP :=
  fun hSW hC hP hF hB => rowNGP_of_formNGVanish hSW hC hP hF hB

end GlobalTheory.NGRowClose
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOneNonGenericRowBoundClosedStatement

section

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem _root_.GlobalTheory.T.corankOneNonGenericRowBound_closed : PI.VolStabS.MassDataS.SWXS → StepChoiceConstantsC → StepPinExists → Formalism.L2.SG.NGVanish.FormNGC → StepThmBPinnedP → RowNGP := by
  first | exact @GlobalTheory.NGRowClose.close | exact GlobalTheory.NGRowClose.close | (intros; apply GlobalTheory.NGRowClose.close <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepPinExistsAndFormNGC

section

@[expose] public section

namespace GlobalTheory

theorem stepPinExists_and_formNGC :
    Formalism.L2.SG.NGAnalytic.StepPinExists ∧ Formalism.L2.SG.NGVanish.FormNGC :=
  ⟨Formalism.L2.SG.NGPin.stepPinExists, Formalism.L2.SG.Pf.formNGC_holds⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeilConstants

section

@[expose] public section

namespace GlobalTheory

theorem rowNGP_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.NGAnalytic.StepThmBPinnedC → Formalism.L2.SG.RowsPos.RowNGP := by
  intro h hB hT
  refine GlobalTheory.T.corankOneNonGenericRowBound_closed (GlobalTheory.St.swxs_of_siegelWeil h) hB GlobalTheory.stepPinExists_and_formNGC.1 GlobalTheory.stepPinExists_and_formNGC.2 ?_
  intro Cg cb Cw cT CT C0 _ _ A
  obtain ⟨CB, h0, a, b, H⟩ := hT Cg cb Cw cT CT C0 A
  exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u u' _ => H C' Cl h1 h2 D large₂ X Y u u'⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil

section

@[expose] public section

namespace GlobalTheory

theorem rowNGP_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsPos.RowNGP :=
  fun h => GlobalTheory.rowNGP_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h (fun _ X u u' hg =>
      Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.analytic_pinnedTheoremB_uniform

end GlobalTheory
end
end
