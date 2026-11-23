module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.RealObjInInfinityXJsz
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCOfOcc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlIntHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlLineHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqAna
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqFam
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowGen1POfConstantsAndPoints
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChainStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SwxsOfSiegelWeil
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepChoiceConstantsCOfSiegelWeilAtInfinity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalCountLineIntegralitySeparation

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem normalCountSteps : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep :=
  ⟨Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine_holds, Formalism.L2.SG.NGCut.NormalIntegrality.NmlInt_holds,
    Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep_holds⟩

end GlobalTheory.Core.One
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalCountLineIntegralitySeparationStatement

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.normalCount_line_integrality_separation : Formalism.L2.SG.NGCut.NormalVectorPairings.NmlLine ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInt ∧ Formalism.L2.SG.NGCut.NormalVectorPairings.NmlSep := by
  first | exact @GlobalTheory.Core.One.normalCountSteps | exact GlobalTheory.Core.One.normalCountSteps | (intros; apply GlobalTheory.Core.One.normalCountSteps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneOnSingletonOfRows

section

@[expose] public section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Diag

theorem mR_eq_m (D : D7) : Formalism.L2.SG.RowsConc.mR D = (D.R.m : ℝ) := by
  have h : 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  unfold Formalism.L2.SG.RowsConc.mR
  rw [h]

theorem log_b_eq (D : D7) (large₂ : SizeData₂ D) : Real.log large₂.sc.b = large₂.sc.L := by
  unfold Formalism.BasicNotions.Scale.b
  exact Real.log_exp _

theorem gamB_eq_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : gamB D large₂ C = gamL D large₂.sc.L C := by
  unfold gamB gamL
  rw [mR_eq_m, log_b_eq]

theorem epsNG_le_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : epsNG D large₂ C ≤ gamL D large₂.sc.L C := by
  unfold epsNG
  have h1 : ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : Real.exp (C * Formalism.L2.SG.RowsConc.mR D ^ 5 * D.R.f * Real.log large₂.sc.b) = gamL D large₂.sc.L C := by
    unfold gamL
    rw [mR_eq_m, log_b_eq]
  rw [h2]
  exact mul_le_of_le_one_left (Real.exp_pos _).le h1

theorem oneOn_singleton_of_rows :
    (RowGen1P → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true) ∧ (GlobalTheory.NGRow.RowNGP → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} false) := by
  constructor
  · intro hG c Cg cb Cu cT CT hcb hcT
    obtain ⟨CB, hCB, C'₀, Cl₀, H⟩ := hG Cg cb Cu cT CT c hcb hcT
    refine ⟨CB, hCB, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r := H C' Cl a1 b1 D large₂ X Y u hT hH hs hC ha
    unfold GeneratorBoundAt at r
    rw [gamB_eq_gamL] at r
    rw [if_pos rfl]
    exact r
  · intro hN c Cg cb Cu cT CT hcb hcT
    obtain ⟨C4, hC4, C'₀, Cl₀, H⟩ := hN Cg cb Cu cT CT c hcb hcT
    refine ⟨C4, hC4, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r : (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).ngSet) ≤ epsNG D large₂ C4 * ddC X Y u u :=
      H C' Cl a1 b1 D large₂ X Y u u hT hH hs hC ha
    rw [if_neg Bool.false_ne_true]
    exact r.trans (mul_le_mul_of_nonneg_right (epsNG_le_gamL D large₂ C4) (Formalism.L2.SG.RowsConc.dd_nonneg hC u u))

end GlobalTheory.Core.Diag
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneOnSingletonOfSiegelWeil

section

@[expose] public section

namespace GlobalTheory.Core.Diag

theorem oneOn_singleton_of_siegelWeil_of_stepChoice :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.NGAnalytic.StepChoiceConstantsC →
      Formalism.L2.SG.Pf.BDat.StepThmBG → Formalism.L2.SG.RowsPos.RowNGP →
      ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false := by
  intro h hB hTB hN c
  have hT : GlobalTheory.SnPos.StepThmBGP := by
    intro Cg cb Cw cT CT C0 _ _ A
    obtain ⟨CB, h0, a, b, H⟩ := hTB Cg cb Cw cT CT C0 A
    exact ⟨CB, h0, a, b, fun C' Cl h1 h2 D large₂ X Y u _ => H C' Cl h1 h2 D large₂ X Y u⟩
  obtain ⟨_h1, _h2, h3, h4, h5, h6, _h7, _h8, _h9⟩ := GlobalTheory.T.equalWords_nonGeneric_estimates_chain
  have hG : GlobalTheory.Core.One.RowGen1P :=
    GlobalTheory.Core.One.rowGen1P_of_siegelWeil_of_points (GlobalTheory.St.swxs_of_siegelWeil h)
      GlobalTheory.T.normalCount_line_integrality_separation.1 GlobalTheory.T.normalCount_line_integrality_separation.2.1 GlobalTheory.T.normalCount_line_integrality_separation.2.2 h3 h4 h5 hB h6 hT
  exact ⟨oneOn_singleton_of_rows.1 hG c, oneOn_singleton_of_rows.2 hN c⟩

end GlobalTheory.Core.Diag
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeil

section

@[expose] public section

namespace GlobalTheory.Core.Diag

theorem oneOn_singleton_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
      ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false :=
  fun h => oneOn_singleton_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h (fun _ X u u' hg =>
      Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz
        CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.bDat_theoremB_global (GlobalTheory.rowNGP_of_siegelWeil h)

end GlobalTheory.Core.Diag
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeilStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.corankOnePairsFamilyBounds_of_siegelWeil : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false := by
  first | exact @GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil | exact GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil | (intros; apply GlobalTheory.Core.Diag.oneOn_singleton_of_siegelWeil <;> assumption)
end
end
