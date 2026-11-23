module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyStepOfFourGlobalLeavesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTupleNondegenerateGramStep
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfSteps

section

@[expose] public section

noncomputable section

open scoped Classical
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRow

theorem exists_row_level_analytic (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticP) : StepAnalyticConstantsP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀),
    fun C' Cl e1 e2 D large₂ X Y u u' hTies hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, hBk',
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u' hTies hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'⟩

end GlobalTheory.NGRow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowLevelWithAnalyticFactsOfStepsStatement

section

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem _root_.GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps : TieOfCtx → StepChoiceConstantsC → StepAnalyticP → StepAnalyticConstantsP := by
  first | exact @GlobalTheory.NGRow.exists_row_level_analytic | exact GlobalTheory.NGRow.exists_row_level_analytic | (intros; apply GlobalTheory.NGRow.exists_row_level_analytic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOnePairsBoundOfSplitFiniteRealRo

section

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowNG_of_cut2P (hc : NGCut2P) : RowNGP := by
  have hR : PN.RowNGJoint := Formalism.FourierDecayAlt.Final.pn_rowNGJoint
  have hC : PN.NGChain := Formalism.FourierDecayAlt.P.norm_chain
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, A, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Cn, hCn, hK⟩ := Formalism.L2.SG.RowsOther.rowNG_of_cut hR hC C1 C0n A CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u u' hTi h0 hs hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hFin, hRe⟩ :=
    h C' Cl a b D large₂ X Y u u' hTi h0 hs hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u') _ _ _ _ (Y.tO u u') D.R.rS D.R.k (Set (TauC Y u u')) (NuC D)
    (NOf2 Y u u' νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hFin hRe
  rw [hdd] at r
  exact r

end GlobalTheory.NGRow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOnePairsBoundOfSplitFiniteRealRoStatement

section

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem _root_.GlobalTheory.T.nonGenericCorankOnePairsBound_of_splitFiniteRealRow : NGCut2P → RowNGP := by
  first | exact @GlobalTheory.NGRow.rowNG_of_cut2P | exact GlobalTheory.NGRow.rowNG_of_cut2P | (intros; apply GlobalTheory.NGRow.rowNG_of_cut2P <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowAnalyticFactsOfFourSteps

section

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticP_of_steps : StepPinExists → StepVanishPinned → StepLocGenPinnedC → StepThmBPinnedP →
    StepAnalyticP := by
  intro hE hV hL hB Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨e₀, f₀, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨v₀, w₀, hV2⟩ := hV Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, p₀, q₀, hB2⟩ := hB Cg cb Cw cT CT C0 hcb hcT A
  refine ⟨CB, CSt, hCB, hCSt, max a₀ (max e₀ (max v₀ p₀)), max b₀ (max f₀ (max w₀ q₀)),
    fun C' Cl h1 h2 D large₂ X Y u u' hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk => ?_⟩
  have ha1 : a₀ ≤ C' := le_trans (by simp) h1
  have ha2 : b₀ ≤ Cl := le_trans (by simp) h2
  have he1 : e₀ ≤ C' := le_trans (by simp) h1
  have he2 : f₀ ≤ Cl := le_trans (by simp) h2
  have hv1 : v₀ ≤ C' := le_trans (by simp) h1
  have hv2 : w₀ ≤ Cl := le_trans (by simp) h2
  have hp1 : p₀ ≤ C' := le_trans (by simp) h1
  have hp2 : q₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨ν, hν⟩ := hE2 C' Cl he1 he2 D large₂ X Y u u' hc
  obtain ⟨s, ng, e1, hs1, hs0, hsb, he0, he3, hLoc, hGen⟩ :=
    hL2 C' Cl ha1 ha2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  exact ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    nuQOK_sc u u' s hs1 hs0 ν hν.1, hν.1, hb0, le_rfl, he0, he3,
    ampVanish_sc Y u u' s hs0 ν (hV2 C' Cl hv1 hv2 D large₂ X Y u u' hc ν hν), hLoc, hGen,
    measureInput_sc Y u u' s ν _ hsb ng,
    hB2 C' Cl hp1 hp2 D large₂ X Y u u' hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν (sc s ν) ng⟩

end GlobalTheory.NGRow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowAnalyticFactsOfFourStepsStatement

section

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem _root_.GlobalTheory.T.rowAnalyticFacts_of_four_steps : StepPinExists → StepVanishPinned → StepLocGenPinnedC → StepThmBPinnedP → StepAnalyticP := by
  first | exact @GlobalTheory.NGRow.stepAnalyticP_of_steps | exact GlobalTheory.NGRow.stepAnalyticP_of_steps | (intros; apply GlobalTheory.NGRow.stepAnalyticP_of_steps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSplitFiniteArchimedeanPartsOfSteps

section

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ngCut2P_of_steps (hM : StepAnalyticConstantsP) (hS : StepSizes) (hC : StepClass) (hN : StepNormals)
    (hP : StepPoints) (hH : StepHeight) : NGCut2P := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hM Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u u' hTies h0 hs hT => ?_⟩
  have hc : Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' := ⟨h0, hs, hT⟩
  have e1' : a₀ ≤ C' := le_trans (by simp) h1
  have e2' : b₀ ≤ Cl := le_trans (by simp) h2
  have f1 : s₀ ≤ C' := le_trans (by simp) h1
  have f2 : t₀ ≤ Cl := le_trans (by simp) h2
  have i1 : n₀ ≤ C' := le_trans (by simp) h1
  have i2 : m₀ ≤ Cl := le_trans (by simp) h2
  have j1 : p₀ ≤ C' := le_trans (by simp) h1
  have j2 : q₀ ≤ Cl := le_trans (by simp) h2
  have k1 : h₀ ≤ C' := le_trans (by simp) h1
  have k2 : j₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨P, iP, B, Irat, Ire, hBk, νL, νB, ng, cSt, e1, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u u' hTies hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u' hc) c1 c2 c3 c4, ?_, hMeas, hSum⟩
  exact ⟨hC D X Y u u' hT νL νB ng, ampInput_of_vanish Y u u' νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u u' hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u u' hc νL νB ng, hLoc, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u u' hc νL νB ng⟩

end GlobalTheory.NGRow
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowSplitFiniteArchimedeanPartsOfStepsStatement

section

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem _root_.GlobalTheory.T.rowSplitFiniteArchimedeanParts_of_steps : StepAnalyticConstantsP → StepSizes → StepClass → StepNormals → StepPoints → StepHeight → NGCut2P := by
  first | exact @GlobalTheory.NGRow.ngCut2P_of_steps | exact GlobalTheory.NGRow.ngCut2P_of_steps | (intros; apply GlobalTheory.NGRow.ngCut2P_of_steps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremi

section

@[expose] public section

open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem GlobalTheory.rowNGP_of_leaves (hCB : StepChoiceConstantsC) (hPin : StepPinExists) (hForm : Formalism.L2.SG.NGVanish.FormNGC)
    (hThmB : StepThmBPinnedP) (hG5 : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) (hW : Formalism.L2.SG.FamDefs.WeightsNG)
    (hG4 : Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) (hEx : Formalism.L2.SG.FamDefs.ExistNG) : RowNGP := by
  obtain ⟨hS0, hNml, hPts, hN1, hX0⟩ := GlobalTheory.RowNGClosed.closedSteps
  have hFam : Formalism.L2.SG.NGLocModel.StepFamC := GlobalTheory.T.familyStep_of_four_globalLeaves hG5 hW hG4 hEx
  have hconds : ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun D =>
    ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1
  have hLoc : StepLocGenPinnedC :=
    stepLocGenPinnedC_of_loc (Formalism.L2.SG.NGLocModel.stepLocPinnedC_of_fam hconds hFam)
  have hVan : StepVanishPinned :=
    stepVanishPinned_of_term (Formalism.L2.SG.NGVanish.stepTermVanish_of_form hForm)
  have hAna : StepAnalyticP := GlobalTheory.T.rowAnalyticFacts_of_four_steps hPin hVan hLoc hThmB
  have hMassData : StepAnalyticConstantsP := GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps (tieOfCtx_of hX0) hCB hAna
  exact GlobalTheory.T.nonGenericCorankOnePairsBound_of_splitFiniteRealRow (GlobalTheory.T.rowSplitFiniteArchimedeanParts_of_steps hMassData sizes_of_hypotheses (stepClass_of_equiv hS0) hNml hPts
    (stepHeight_of_normOne hN1))
end
end
