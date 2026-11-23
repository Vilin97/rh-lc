module

public import Development.AutomorphicArithmetic.CharacterBoxes.ZeroFreeAllOfTopG
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShapeAlt
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
public import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchAllMembers
public import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PStmtFree
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PacketStatementOfIndependence
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntegralAtT0Lattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalLinkOfBranchIdentitiesAndMultiplicity
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.SharpRestriction.GlobalSchurBounds.LemmaBSecondBranchOfLength
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll
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
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfGappedMultiplicity
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
public import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
public import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV
public import Formalism.SharpRestriction.MuTuOfTuSize
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClosedFamilyAdmissibleTwistLink
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Link
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkAltAltBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkBrest
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkEta
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkEx
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassOfRecordOfChoice
public import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
public import Formalism.SharpRestriction.SmoothDesignExistence.AdmissibleTopsMertens
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkIrr
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelectionClosedOfWuDecay
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WireSel
import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.RamifiedLevelZeroHolds

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}

theorem ramified_level_zero_holds (Fm : FamP eps) (tT : FamU Fm ConcreteFormsLevelZero) : FamU Fm LocalLatticeBases.HeckeRamifiedLevelZero :=
  tT.mono fun D u hS h => UnramifiedTrace.hecke_ramified_zero_all D u hS h

end Formalism.MainNotions

end
end
end

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.TuSizeOfRealPlaceSecondLayer

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

variable {eps : ℝ}


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem Wire.famGLmin_of_realPlaceSecondLayer (𝒞 : FamClass) (tie : Closed 𝒞 fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (hU : ∀ D, MassRatioUnderVolume D) (hG : ∀ D, GenusMassVolumes.GenusMassAt D 2) :
    Wire.FamGLmin 𝒞 4 := by
  exact {
    h2b := Closed.of_all fun Fm _ => GenusMassVolumes.siegel_mass_ratio_family Fm
    h2v := tie.imp fun Fm _ _ t => family_property_mono (family_conditions_of_layer_two Fm t).1 fun D hT =>
      GenusMassVolumes.volume_eq_mass_rank_two D (StandardLattice.volumeMass_of_unfolding D (hU D hT)) (GenusMassVolumes.volume_mass_of_genus_rank D 2 hT (hG D))
    h3 := Closed.of_all fun Fm _ => GappedMultiplicityBounds.explicit_bound_family Fm
    hZa := Closed.of_all fun Fm _ => TraceIntegrality.lower_slope_inequality_family Fm
    hZb := Closed.of_all fun Fm _ => TraceIntegrality.slope_inequality_family_four Fm
    tCV := tie.imp fun Fm _ _ t => tCV_of_ties Fm (family_conditions_of_layer_two Fm t).2.1
    hW := tie.imp fun Fm _ _ t =>
      (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).1
    hμ := tie.imp fun Fm _ _ t =>
      (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).2.1
    hI := tie.imp fun Fm _ _ t => hI_tied Fm (family_conditions_of_layer_two Fm t).2.2 PI.IntegralAtBasePointLattice.integral_at_t0_lattice
    hR := tie.imp fun Fm _ _ t => ramified_level_zero_holds Fm (family_conditions_of_layer_two Fm t).2.2
    hB := tie.imp fun Fm _ _ t =>
      (slope_free_branch_family Fm (family_conditions_of_layer_two Fm t).2.2 freeTT_holds slopeLineT_holds LemB.second_branch_all_members).2.2
  }

end Formalism.MainNotions

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkGl

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4



theorem GlobalTheory.Top.link_gl : ∀ (𝒜 : FamClass)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm)
    (tie : Closed (D3 3 𝒜) fun Fm _ => RealPlaceSecondLayerConditions Fm)
    (hU : ∀ D, MassRatioUnderVolume D)
    (hG : ∀ D, GenusMassVolumes.GenusMassAt D 2), (Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm) ∧ (Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0) := by
  intro 𝒜 hduty tie hU hG
  have hC0 : (3 : ℝ) ≤ 3 := le_refl _
  have hC0' : (0 : ℝ) < 3 := by norm_num
  have hCe : Real.exp 1 ≤ 3 := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hC0
  have hCabs : (0 : ℝ) ≤ 2 := by norm_num
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  have hGLm := Formalism.MainNotions.Wire.famGLmin_of_realPlaceSecondLayer (D3 3 𝒜) tie hU hG
  have hRk : Closed (D3 3 𝒜) fun Fm CH => ChosenE Fm 3 CH → NuFullF Fm ∧ J.MuRank Fm :=
    ((hGLm.muRank 3 hC0').and
      (Closed.of_class (P := fun Fm _ => TuSize Fm) fun _ _ hc => hc.2.2.1)).imp fun _ _ _ h c => h.1 h.2 c
  have hGL : Closed (D3 3 𝒜) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm 2 CH 3 2 0 :=
    hGLm.link8 2 3 hCabs hC0 fun Fm hc => (hduty Fm (d3_a hc)).2.2.2.2.1
  exact ⟨hRk, hGL⟩

end
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.DesWin

section

@[expose] public section

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions

theorem topDesWin (𝒞 𝒞' ℰ : FamClass) (Cabs C0 eD eL : ℝ) (hEx : DesignExists (WithTw (WithSm 𝒞')) C0)
    (h1 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm) (h2 : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → ℰ Fm)
    (hV : ∀ {eps : ℝ} (Fm : FamP eps), ℰ Fm → HypV Fm.toFamCore)
    (hN : Closed (Des 𝒞 C0) fun Fm _ => LinkN Fm)
    (hEta : Closed (Des 𝒞 C0) fun Fm _ => LinkEta Fm)
    (hIRR : Closed (Des 𝒞 C0) fun Fm _ => LinkIRR Fm)
    (hZ : Closed (Des 𝒞 C0) fun Fm _ => SmallLevelRankEq Fm)
    (hDIV : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH)
    (hRk : Closed (Des 𝒞 C0) fun Fm CH => ChosenE Fm C0 CH → NuFullF Fm ∧ J.MuRank Fm)
    (hG : Closed (Des 𝒞 C0) fun Fm _ => LinkG Fm)
    (hS : Closed (Des 𝒞 C0) fun Fm _ => TuSize Fm → LinkS Fm C0)
    (hGL : Closed (Des 𝒞 C0) fun Fm CH => TuSize Fm → DGamSize Fm → LinkGLOBAL Fm Cabs CH C0 eD eL) : FamilyClassConnected ℰ := by
  obtain ⟨ε1, hε1, hA⟩ := hN.and (hDIV.and (hEta.and (hIRR.and (hZ.and (hRk.and (hG.and (hS.and hGL)))))))
  obtain ⟨ε3, hε3, hEx⟩ := hEx
  refine ⟨eD, eL, min ε1 ε3, lt_min hε1 hε3, fun ε h0 hlt => ?_⟩
  obtain ⟨K, hK⟩ := hA ε h0 (le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _)))
  obtain ⟨Fm, CH, hc, -, hL, hCh, hT, hDG⟩ := hEx ε h0 (le_of_lt (lt_of_lt_of_le hlt (min_le_right _ _))) K
  obtain ⟨aN, aD, aE, aI, aZ, aR, aG, aS, aGL⟩ := hK Fm CH ⟨⟨⟨h1 Fm hc.1.1, hc.1.2⟩, hc.2⟩, ⟨CH, hCh⟩, hT, hDG⟩ hL
  have hD := aD hT hDG aE (divinN_of_hypV Fm h0 (hV Fm (h2 Fm hc.1.1)) aN aZ)
  exact ⟨Fm, h2 Fm hc.1.1, aGL hT hDG hCh ⟨aG, aS hT, aI, hD,
    J.linkMu_of_linkDIV Fm hD (aR hCh).1 (aR hCh).2 (muTu_of_tuSize Fm h0 hT) (J.muDGam_of_fact Fm hDG)⟩⟩

end UpperTheory.Top

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkG

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.closed_linkG_of_duty : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkG Fm := by
  intro 𝒜 sel hduty
  have hRec : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → _root_.Formalism.L2.SecondLayerFamilyClass Fm := fun Fm hc =>
    _root_.Formalism.L2.Top3.layerTwoFamilyClass_of_linked_aligned (sel Fm hc) (_root_.Formalism.L2.Top3.linkedFamiliesAligned_of_duty (sel Fm hc) (hduty Fm hc))
  have hG2 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.G.Adm2F Fm :=
    Closed.of_class fun Fm _ hc => admissible_tops_mertens Fm (topsF_of_chosenE Fm hc.2.1.choose_spec)
  have hGt : Closed (D3 3 𝒜) fun Fm _ => Formalism.L2.G.GroupCompatibilityFamily Fm :=
    Closed.of_class fun Fm _ hc => _root_.Formalism.L2.group_compatibility_of_second_layer_family Fm (hRec Fm (d3_a hc))
  have lG := Formalism.L2.G.linkG_concrete5 (D3 3 𝒜) hGt hG2
  exact lG
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopShape

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem UpperTheory.Top.shape_closed_link_n_of_green : GlobalTheory.GLq.Green → _root_.GlobalTheory.Fc.TopShapeAlt True True (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) UpperTheory.Top.TopG := by
  intro hGreen 𝒜 cT hEx sel hduty selS selP selDH selC selB hRB hTw hPA hLamP hDivG hDcPtG hTu hn4 hLit hVC hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR selJ jOn hMt rRows aPt0 aPtTw aPer0 aPerTw aP10 aAtG aC2 hServ nR nRest cIc hcI irrC zL tie hU hG la G hla hH hV
  have hgl := GlobalTheory.Top.link_gl 𝒜 hduty tie hU hG
  have bRest := _root_.GlobalTheory.Top.link_brest_alt 𝒜 sel selS selP selDH selC selB hRB hPA hDivG hDcPtG rRows tie
  have hCsz : Closed (D3 3 𝒜) fun Fm _ => 0 ≤ Fm.Csz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 𝒜) fun _ => 0
  have oneMap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) ((_root_.Formalism.L2.Top4.SingleMapCondition selB) Fm (d3_a hc)) :=
    Closed.of_class fun Fm _ _ hc => ⟨0, fun x hx h _ i j => (hRB Fm (d3_a hc) x hx h i).oneMap j⟩
  have hA2 := _root_.GlobalTheory.Top.closed_family_admissible_twist_link_alt 𝒜 sel aPt0 aPtTw aPer0 aPerTw aP10 aAtG hServ
  have hC5 := _root_.GlobalTheory.Top.selection_closed_of_wu_decay_alt 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have hBR : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, TuSize Fm → DGamSize Fm →
      _root_.Formalism.L2.DIV.DivisionKernelConstantBounds Fm (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA Fm hc) 2 CH :=
    (bRest.and ((Closed.of_class fun Fm _ hc => cut_of_stable (hMt Fm (d3_a hc))).and (rRows.and (oneMap.and (hCsz.and (hA2.and (aC2.and hC5))))))).imp
      fun Fm CH _ ⟨r, o, rr, om, cz, a, c, c5⟩ hc hT hD =>
        (r hc hT hD).toRows_alt (fun hN => _root_.GlobalTheory.Top.wire_sel_alt 𝒜 sel selS selP selDH selC selB hTw hPA hDivG hDcPtG Fm hc CH cz hD (rr hc) (om hc) (r hc hT hD).bu hN) o a (complement_two_of_items c) c5
  have hDIV := _root_.Formalism.L2.DIV.closed_linkDIVt_of_closed_bridge_kernel (D3 3 𝒜) 2 (_root_.Formalism.L2.Top4.RankOfDivisionKernel sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA) hBR
  have hsub : ∀ {eps : ℝ} (Fm : FamP eps), WithTw (WithSm (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm)) Fm →
      WithTw (WithSm (WithChN 𝒜)) Fm := fun _ hc => ⟨⟨⟨hc.1.1.1.1, hc.1.1.2⟩, hc.1.2⟩, hc.2⟩
  have hE := _root_.GlobalTheory.Top.designExists_of_tuSize_aux4n_litThin (fun Fm => 𝒜 Fm ∧ G.cls la Fm) cT (fun hM => hEx hM la G hla hH) (fun Fm hc => sel Fm hc.1)
    (fun Fm hc => hduty Fm hc.1) (Pk.Closed.sub hTu hsub) (Pk.Closed.sub hn4 hsub) hLit
  exact UpperTheory.Top.topDesWin (WithChN 𝒜) (WithChN fun Fm => 𝒜 Fm ∧ G.cls la Fm) (G.cls la) 2 3 2 0 hE
    (fun _ hc => ⟨hc.1.1, hc.2⟩) (fun _ hc => hc.1.2) hV nRest (_root_.GlobalTheory.Top.closed_linkEta_of_duty 𝒜 sel hduty)
    (_root_.GlobalTheory.Top.Irr.closed_linkIRR_of_join_count hGreen 𝒜 sel cIc hcI irrC) (_root_.GlobalTheory.Top.link_alt_alt_alt 𝒜 sel selS selP selDH selC selB hPA hLamP hDivG zL) hDIV hgl.1 (_root_.GlobalTheory.Top.closed_linkG_of_duty 𝒜 sel hduty)
    (_root_.GlobalTheory.Top.link_alt_alt_bis 𝒜 sel selS hWu hRF hTF c30 hc30 sTy sNG sM sLp sO h30 hInstR) hgl.2
end
end
end
end
