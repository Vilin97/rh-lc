module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
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
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedSteps

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

noncomputable section

open scoped Classical

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticCGP_of_steps : StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP →
    StepAnalyticCGP := by
  intro hE hV hL hB Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨e₀, f₀, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨v₀, w₀, hV2⟩ := hV Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, p₀, q₀, hB2⟩ := hB Cg cb Cw cT CT C0 hcb hcT A
  refine ⟨CB, CSt, hCB, hCSt, max a₀ (max e₀ (max v₀ p₀)), max b₀ (max f₀ (max w₀ q₀)),
    fun C' Cl h1 h2 D large₂ X Y u hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk => ?_⟩
  have ha1 : a₀ ≤ C' := le_trans (by simp) h1
  have ha2 : b₀ ≤ Cl := le_trans (by simp) h2
  have he1 : e₀ ≤ C' := le_trans (by simp) h1
  have he2 : f₀ ≤ Cl := le_trans (by simp) h2
  have hv1 : v₀ ≤ C' := le_trans (by simp) h1
  have hv2 : w₀ ≤ Cl := le_trans (by simp) h2
  have hp1 : p₀ ≤ C' := le_trans (by simp) h1
  have hp2 : q₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨ν, hν⟩ := hE2 C' Cl he1 he2 D large₂ X Y u u hc
  obtain ⟨s, ng, e1, hs1, hs0, hsb, he0, he3, hLoc, hGen⟩ :=
    hL2 C' Cl ha1 ha2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  exact ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    Formalism.L2.SG.NGAnalytic.nuQOK_sc u u s hs1 hs0 ν hν.1, hν.1, hb0, le_rfl, he0, he3,
    ampVanishG_sc Y u s hs0 ν (ampVanishG_of_term Y u ν (hV2 C' Cl hv1 hv2 D large₂ X Y u hc ν hν)), hLoc, hGen,
    measureInputG_sc Y u s ν _ hsb ng,
    hB2 C' Cl hp1 hp2 D large₂ X Y u hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν (sc s ν) ng⟩

end GlobalTheory.SnPos
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedStepsStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps : StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP → StepAnalyticCGP := by
  first | exact @GlobalTheory.SnPos.stepAnalyticCGP_of_steps | exact GlobalTheory.SnPos.stepAnalyticCGP_of_steps | (intros; apply GlobalTheory.SnPos.stepAnalyticCGP_of_steps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositive

section

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticGP_of (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticCGP) : StepAnalyticGP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hD hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hD hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7,
    a8, a9, a10, a11⟩

end GlobalTheory.SnPos
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositiveStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.analyticGenericBound_of_choiceStep_positive : TieOfCtx → StepChoiceConstantsC → StepAnalyticCGP → StepAnalyticGP := by
  first | exact @GlobalTheory.SnPos.stepAnalyticGP_of | exact GlobalTheory.SnPos.stepAnalyticGP_of | (intros; apply GlobalTheory.SnPos.stepAnalyticGP_of <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositive

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowMainEqP_of_cut (hCh : PN.NGChain) (hMG : MeanAmpGen) (hc : GenCutP) : RowMainEqP := by
  intro Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨C1, C0n, Aexp, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh hMG C1 C0n Aexp CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u hTies hH hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hIn⟩ :=
    h C' Cl a b D large₂ X Y u hTies hH hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (Y.tO u u) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOfG Y u νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hIn
  rw [hdd] at r
  exact r

end GlobalTheory.SnPos
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositiveStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.equalWordGenericBound_of_cutBound_positive : PN.NGChain → MeanAmpGen → GenCutP → GlobalTheory.SnPos.RowMainEqP := by
  first | exact @GlobalTheory.SnPos.rowMainEqP_of_cut | exact GlobalTheory.SnPos.rowMainEqP_of_cut | (intros; apply GlobalTheory.SnPos.rowMainEqP_of_cut <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimates

section

@[expose] public section

noncomputable section

open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genCutP_of_steps (hS : StepSizes) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hH : StepHeightG) (hA : StepAnalyticGP) : GenCutP := by
  intro Cg cb Cw cT CT C0 A0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u hTies hHy hT => ?_⟩
  have hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hHy.1, hHy.2.1, hT⟩
  have e1' : a₀ ≤ C' := le_trans (le_max_left _ _) h1
  have e2' : b₀ ≤ Cl := le_trans (le_max_left _ _) h2
  have f1 : s₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1
  have f2 : t₀ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h2
  have i1 : n₀ ≤ C' :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h1
  have i2 : m₀ ≤ Cl :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h2
  have j1 : p₀ ≤ C' := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have j2 : q₀ ≤ Cl := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  have k1 : h₀ ≤ C' := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have k2 : j₀ ≤ Cl := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  obtain ⟨P, iP, B, Irat, Ire, νL, νB, ng, cSt, e1, hBk, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u hTies hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    Formalism.L2.SG.NGCut.ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u hc) c1 c2 c3 c4, ?_⟩
  exact ⟨classInputG_of Y u (hC D X Y u (g_ge_three hc) hT) νL νB ng, ampInputG_of_vanish Y u νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u hc νL νB ng, hLoc, hMeas, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u hc νL νB ng, hSum⟩

end GlobalTheory.SnPos
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimatesStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

theorem _root_.GlobalTheory.T.generic_height_bound_of_local_estimates : StepSizes → StepClassG → StepNormalsG → StepPointsG → StepHeightG → StepAnalyticGP → GenCutP := by
  first | exact @GlobalTheory.SnPos.genCutP_of_steps | exact GlobalTheory.SnPos.genCutP_of_steps | (intros; apply GlobalTheory.SnPos.genCutP_of_steps <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedSteps

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

theorem rowMainEqP_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBGP) : GlobalTheory.SnPos.RowMainEqP :=
  GlobalTheory.T.equalWordGenericBound_of_cutBound_positive hCh Formalism.L2.SG.Pf.MainEqCut.meanAmplitudeGeneric_holds
    (GlobalTheory.T.generic_height_bound_of_local_estimates Formalism.L2.SG.NGCut.sizes_of_hypotheses hC hN hP (stepHeightG_of_normOne hO)
      (GlobalTheory.T.analyticGenericBound_of_choiceStep_positive hTi hB (GlobalTheory.T.analyticConstantGenericBound_of_normalisedSteps hE hV hL hT)))

end GlobalTheory.SnPos
end
end
