module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultQ
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDataExtendLargerFieldsOfPublishedStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeightSetResidueCharacteristic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllStagesAtMemberOfSpecializations
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutomorphyOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExBLIsLinkedPrmRStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteLevelAndSecond
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberEClosing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerUpStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPrmRNelStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendsFineAdelicDatumToLargerFieldOfHyp

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem datExt_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExt :=
  fun h1 h2 h3 h4 h5 h6 h7 => datExt_of_datExt0 (GlobalTheory.T.adelicData_extend_largerFields_of_hypotheses h1 h2 h3 h4 h5 h6 h7)

end GlobalTheory.Mem.R3.Rw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendsFineAdelicDatumLargerFieldOfPublishedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.fineAdelicDatum_extends_to_larger_field_of_hypotheses : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → DatExt  := by
  first | exact @GlobalTheory.Mem.R3.Rw.datExt_of_hypotheses | exact GlobalTheory.Mem.R3.Rw.datExt_of_hypotheses | (intros; apply GlobalTheory.Mem.R3.Rw.datExt_of_hypotheses <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Has3NeoOfSteps

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.Top.Bl
theorem has3_neo_of_localLanglands_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (hB : ExistsUnlocalizedSaturatedState) (hA : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL) (hMt : SMt) (hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL)
    (hCu : _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL) (hB0 : _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep) (hB1 : _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep) (hB2 : _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep) (hC : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL) (hFin : _root_.GlobalTheory.HeightCounting.Up.SpectralFiniteness hL cDep)
    (S : SExt) (Γ : GeoP) : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s) := by
  have h := StepW.and hB (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
  refine h.trans (StepW.of_all ?_)
  intro K B f T w _ _ H
  obtain ⟨⟨P, x, sat, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
  obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
  obtain ⟨imt⟩ := mt P x1
  obtain ⟨irat⟩ := rat P x1 la
  have li : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
  obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
  obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
  obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
  obtain ⟨sc⟩ := c P x4 l2
  obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ ⟨p4 (p3 p2), sat⟩
  exact ⟨Z, ⟨v⟩⟩
end GlobalTheory.Mem.Top.Bl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lv3StageMovesSpectral

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.HeightCounting.Up

theorem kept_trans_layer {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''} (h : Kept c c') (h' : Kept c' c'') :
    Kept c c'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om, h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    ⟨h.set.cc.trans h'.set.cc, h.set.Tw.trans h'.set.Tw, h.set.l.trans h'.set.l, h.set.O0.trans h'.set.O0, h.set.crO0.trans h'.set.crO0, h.set.algO0.trans h'.set.algO0, h.set.topO0.trans h'.set.topO0, h.set.O.trans h'.set.O, h.set.crO.trans h'.set.crO, h.set.algO.trans h'.set.algO, h.set.Ok.trans h'.set.Ok, h.set.crOk.trans h'.set.crOk, h.set.algOk.trans h'.set.algOk, h.set.zk.trans h'.set.zk, h.set.pD.trans h'.set.pD, h.set.chi1.trans h'.set.chi1, h.set.Sig.trans h'.set.Sig, h.set.finSig.trans h'.set.finSig, h.set.jS.trans h'.set.jS, h.set.side.trans h'.set.side, h.set.rhoS.trans h'.set.rhoS, h.set.S0.trans h'.set.S0, h.set.hEig.trans h'.set.hEig, h.set.abelian₂.trans h'.set.abelian₂, h.set.sideL.trans h'.set.sideL, h.set.RCG.trans h'.set.RCG, h.set.grpRCG.trans h'.set.grpRCG, h.set.finRCG.trans h'.set.finRCG, h.set.art.trans h'.set.art, h.set.th.trans h'.set.th⟩,
    ⟨h.forms.Fm.trans h'.forms.Fm, h.forms.acgFm.trans h'.forms.acgFm, h.forms.modFmK.trans h'.forms.modFmK, h.forms.modFmO.trans h'.forms.modFmO, h.forms.actG.trans h'.forms.actG, h.forms.U.trans h'.forms.U, h.forms.psiU.trans h'.forms.psiU, h.forms.eAlg.trans h'.forms.eAlg, h.forms.Dat.trans h'.forms.Dat, h.forms.th.trans h'.forms.th, h.forms.lev.trans h'.forms.lev, h.forms.thPsi.trans h'.forms.thPsi, h.forms.MtV.trans h'.forms.MtV, h.forms.acgMt.trans h'.forms.acgMt, h.forms.modMtK.trans h'.forms.modMtK, h.forms.modMtO.trans h'.forms.modMtO, h.forms.MtLat.trans h'.forms.MtLat, h.forms.thP.trans h'.forms.thP, h.forms.hkF.trans h'.forms.hkF⟩,
    h.br.trans h'.br, h.twI.trans h'.twI, h.sd.trans h'.sd, h.Q.trans h'.Q, h.k.trans h'.k, h.psi.trans h'.psi⟩


end GlobalTheory.HeightCounting.Up
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OrgOfKept

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.HeightCounting.Up
theorem org_of_kept_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {cDep : ℝ} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {D D' : D7} {Wt : Set B.places.Pl} {nch : NChoice D} {nch' : NChoice D'}
    (h : _root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch) (hk : Kept nch nch') : _root_.GlobalTheory.HeightCounting.Up.OriginData hL cDep K w Wt nch' := by
  obtain ⟨P, x, l, h1, h2, h3⟩ := h
  exact ⟨P, x, l, h1, h2, kept_trans_layer h3 hk⟩

theorem lv3Mv_extensionWithOrigin_and_nEog : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s ∧ LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s := by
  intro hL cDep S Γ
  constructor
  · intro K B f T w Z l S' N h
    have htransport := _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := htransport
    have hchoice := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨nch', xd', hk, -, hn, -, hnx⟩ := hchoice
    have hnnew := hn l.n
    obtain ⟨n'⟩ := hnnew
    have hrxnew := hrx ⟨l.rx⟩
    obtain ⟨rx'⟩ := hrxnew
    have hdata := l.nx
    obtain ⟨c, ⟨e, ⟨pin⟩⟩, ⟨org⟩⟩ := hdata
    have hnxnew := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    obtain ⟨⟨c', e'⟩⟩ := hnxnew
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨e', ⟨pin'⟩⟩, ⟨_root_.GlobalTheory.HeightCounting.Up.org_of_kept_alt org hk⟩⟩, hpk⟩
  · intro K B f T w Z l S' N h
    have htransport := _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices K B f T w Z l.Wt l.p0 l.what₂ S' N h
    obtain ⟨p0', t', hs, hgeo, hpk, hrx⟩ := htransport
    have hchoice := _root_.GlobalTheory.T.exists_kept_choice_upper_lattice_alt hL K B f T w Z l.Wt S' N h l.nch l.xd
    obtain ⟨nch', xd', hk, -, hn, hg, hnx⟩ := hchoice
    have hnnew := hn l.n
    obtain ⟨n'⟩ := hnnew
    have hrxnew := hrx ⟨l.rx⟩
    obtain ⟨rx'⟩ := hrxnew
    have hdata := l.nx
    obtain ⟨c, ⟨⟨e, ⟨pin⟩⟩, ⟨org⟩⟩, ⟨good⟩⟩ := hdata
    have hnxnew := hnx l.p0 l.what₂ l.n p0' t' n' hs hgeo ⟨c, e⟩
    obtain ⟨⟨c', e'⟩⟩ := hnxnew
    have pin' := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z l.Wt S' N h l.p0 l.what₂ p0' t' hs pin
    exact ⟨Lv3.mk ⟨l.g, l.coh, l.Wt, p0', t', rx'⟩ nch' n' xd'
      l.chiT ⟨c', ⟨⟨e', ⟨pin'⟩⟩, ⟨_root_.GlobalTheory.HeightCounting.Up.org_of_kept_alt org hk⟩⟩, ⟨hg good⟩⟩, hpk⟩
end GlobalTheory.HeightCounting.Up
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OrgOfKeptStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.lv3Mv_extensionWithOrigin_and_NEog : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (S : SExt) (Γ : GeoP), LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) S Γ).s ∧ LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep) S Γ).s := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.lv3Mv_extensionWithOrigin_and_nEog | exact _root_.GlobalTheory.HeightCounting.Up.lv3Mv_extensionWithOrigin_and_nEog | (intros; apply _root_.GlobalTheory.HeightCounting.Up.lv3Mv_extensionWithOrigin_and_nEog <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsBaseLatticeOfPrime

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.Top.Bl
theorem exists_baseLattice_of_pair_alt (hA : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt) (hE : _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis) (hH : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hN : _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL) (N Ng : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL)
    (toB : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c))
    (toN : ∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c →
      Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd)
    (has3 : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s))
    (lv : LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (lvg : LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s)
    (intersection_update_fsHerm_neg_one : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s)
    (second : Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) fun K B f T =>
      ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s K B f T w)
    (hMQ : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry))) :
    MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s)
        (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry))) := by
  have exp := _root_.GlobalTheory.T.automorphy_of_hypotheses_alt_alt hE.e1 hE.e2 hE.e3 hE.e4 hE.e5 hE.e6 hE.e7 hE.e8 hE.e9 hE.e10 hE.e11 hE.e12 hE.e13 hA.a6 hE.e14 hA.a22
    hE.e15 hE.e16 hE.e17 hE.e18 hE.e19 hE.e20 hE.e21 hE.e22 hE.e23 hE.e24 hE.e25 hN.pr hN.ser hL hN.parMem N
    SExt.none (geoCl anyGeometry) toB
  refine ⟨?_, ?_⟩
  · exact _root_.GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt hA.a1 hA.a2 hA.a3 hA.a11 hA.a10 hA.a6 hA.a12 hA.a13 hA.a14 hA.a16 hA.a17 hA.a18 hA.a8 hA.a6 hA.a7
      hA.a5 hA.a19 hA.a20 hA.a21 hL N Ng has3 lv lvg exp second toN
  · exact _root_.GlobalTheory.T.geometric_parameter_uniform_alt hH.h1.q12 hH.cover hA.a5 hA.a7 hA.a8 hA.a9 hA.a10 hA.a6 hA.a22 hA.a23 hA.a1 hL N (geoCl anyGeometry)
      (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)) rfl toB intersection_update_fsHerm_neg_one hMQ
theorem exists_baseLattice_of_prime_alt : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL → ∀ cDep : ℝ,
    _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s)
        (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry))) := by
  intro hA hE hH hW hL hN cDep hMQ
  have holdsW : WeightCaseCondition := _root_.GlobalTheory.T.w_of_weight_residue_char hH.h1 hH.h3 hH.multW
  have datE : DatExt := GlobalTheory.T.fineAdelicDatum_extends_to_larger_field_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  obtain ⟨sA, sMt, sRat, sCusp, -, -, -, sC, -, stages⟩ :=
    _root_.GlobalTheory.T.all_stages_at_member_of_specializations_alt
      hA.a7 hA.a5 hA.a8 hA.a9 hA.a12 hH hN.pr hN.ser hL hN.arch hN.pt
  obtain ⟨settings, series, points, finiteness⟩ := stages cDep
  obtain ⟨fin, second⟩ := _root_.GlobalTheory.T.sFino_and_secondNo_of_sFinl'
    hH.cover hA.a7 hA.a5 hN.pr hN.ser datE holdsW hA.a9 hN.arch.pht hL sMt sRat sCusp cDep finiteness
  have has3 := _root_.GlobalTheory.Mem.Top.Bl.has3_neo_of_localLanglands_alt
    hL cDep hW sA sMt sRat sCusp settings series points sC fin SExt.none (geoCl anyGeometry)
  have lv := _root_.GlobalTheory.T.lv3Mv_extensionWithOrigin_and_NEog hL cDep SExt.none (geoCl anyGeometry)
  refine exists_baseLattice_of_pair_alt hA hE hH hL hN
    (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep)
    (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep)
    ?_ ?_ has3 lv.1 lv.2
    (_root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl hL cDep anyGeometry)
    (second SExt.none (geoCl anyGeometry)) hMQ
  · intro K B f T w Z Wt p0 t nch n xd c h
    exact ⟨h.1.1⟩
  · intro K B f T w Z Wt p0 t nch n xd c h
    exact ⟨⟨h.1⟩, h.2.down⟩
end GlobalTheory.Mem.Top.Bl
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.member_exists_baseLattice_alt : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL → ∀ cDep : ℝ, _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s ∧ GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry))) := by
  exact _root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt
end
end
end
end
