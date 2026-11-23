module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
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
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LargeBaseRayCondition
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ClassSumPinOfReadAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeNumerical
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreTiesOfTied
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PathCoreConditionsOfParametersFreeConditionsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowETiesB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SidePtPartOfPackStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupAllUsedPart

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreSlotRX

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug

theorem coreCondition_RX : ∀ (𝒮 : Slots), 𝒮.Rx = RX → CoreSlot 𝒮 := by
  intro 𝒮 h K B f T w Z Wt p0 t hx
  rw [h] at hx
  exact ⟨hx.laws, hx.canon, hx.rank, hx.pb⟩

end GlobalTheory.Plug
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisorAll

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoTies

theorem twAllAt_tr {D : D7} (N : ∀ u, Submodule (NumberField.RingOfIntegers D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    {x : NChoice D} {y : ThData D} (H : DQ.TwAllAt D x y) : DQ.TwAllAt (setDiv D N h) (nchTr N h x) (xdTr N h y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, fun a ha => ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2 a ha
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr N h _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

theorem twAll_pt {K : Ctx} (β : BPt K) : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAllAt_tr (nPrime β.p.L) β.p.ht β.twAll


end GlobalTheory.GeoTies
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HasExpOfLayer

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
namespace GlobalTheory.ExpTiesOfLayer
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem hasExp_of_layer_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists), _root_.GlobalTheory.PlugPt.HasExponent' (_root_.GlobalTheory.HeightCounting.defaultExtension hL) ∧ ∀ (E : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL), (∀ K B f T w Z Wt p0 t nch n xd c, E K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.defaultExtension hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.PlugPt.HasExponent' E := by
  intro hL
  have hNE : _root_.GlobalTheory.PlugPt.HasExponent' (_root_.GlobalTheory.HeightCounting.defaultExtension hL) := by
    intro K B f T w Z Wt p0 t nch n xd c y
    have hg := c.row.grp
    refine ⟨⟨⟨⟨⟨y.ser.ex⟩, ⟨fun g => (hg.lvl0 g).symm, ?_⟩, ?_⟩⟩, PUnit.unit⟩⟩
    · intro i b u hu
      obtain ⟨x, hx, hx'⟩ := hg.psi0 u hu i b
      exact ⟨x, hx, hx'⟩
    · intro i j b a _
      rw [y.xd i ((j : ℕ) + 1) b (by omega) (by omega)]
      exact Set.mem_univ _
  exact ⟨hNE, fun E hE K B f T w Z Wt p0 t nch n xd c e => by
    obtain ⟨y⟩ := hE K B f T w Z Wt p0 t nch n xd c e
    exact hNE K B f T w Z Wt p0 t nch n xd c y⟩
end GlobalTheory.ExpTiesOfLayer
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtRealised

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem pt_realised_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : b.pt.RealisedCondition :=
  ⟨b.R, b.S, b.B, b.pins, b.Rr, b.recPins, rfl⟩
theorem pt_T_pb_eq_R_pb {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : b.pt.T.pb = b.pt.R.C.P.pb :=
  GlobalTheory.PinsFixHalf.pb_eq_of_pins b.pt.T b.pt.R.toRealDat b.pt.κ b.pt.v₀ b.pt.O b.pt.charW.base.lev b.pt.fw.laws b.pt.pins
theorem pt_realised_and_pb_eq : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), b.pt.RealisedCondition ∧ b.pt.T.pb = b.pt.R.C.P.pb :=
  fun _ _ _ b => ⟨_root_.GlobalTheory.Fc.Ind.pt_realised_alt b, _root_.GlobalTheory.Fc.Ind.pt_T_pb_eq_R_pb b⟩
end GlobalTheory.Fc.Ind
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.EventuallyConstructedPointHostSizeParametersNumericaStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.eventually_constructedPoint_hostSize_numerical : EvP fun _ K => ∀ β : BPt K, GlobalTheory.FieldSize.HostSz β.D.host β.O.L.sc.L ∧ ∀ C, FieldTies β.D C → NumAtL β.O.L K.s.x := by
  first | exact @GlobalTheory.Plug.eventually_hostSize_and_numAt | exact GlobalTheory.Plug.eventually_hostSize_and_numAt | (intros; apply GlobalTheory.Plug.eventually_hostSize_and_numAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.MoreOfTiesB

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

theorem more_of_tiesB : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c),
    TiesB D O c b → FieldSmall D O.L → SingleIndexPlacesAreTwisted b → More b := by
  intro D O c b hT hS hW
  obtain ⟨hs, hr⟩ := hT
  refine ⟨hW, ?_, ?_⟩
  · exact GlobalTheory.Plug.coreTies_of_tied D _ _ _ _ O.L O.ex.errX b.T (R2 b) b.P.A3.A.μ0 hs.tied b.charW.base.lev hS
  · exact ⟨hs.series, hs.level, hs.data, hs.psi, hs.psiVal, hs.small, hs.types, hr⟩

end GlobalTheory.PlugPt
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowEPartTies

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem rowE_part_ties_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (Q : V4.Slot),
    CoreSlot 𝒮 → RowE (Bd := _root_.GlobalTheory.Fc.Ind.PointSummands) (sAnd Q RayPosition) (linkOf fun K p c b => _root_.GlobalTheory.PlugPt.pinnedPointOfReading ν K p c b.pt)
      fun _ D O c b => TiesB D O c b.pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ More b.pt := by
  intro hR hL 𝒮 ν Q hC
  refine (EvP.and (_root_.GlobalTheory.PlugPt.rowE_tiesB_alt hR hL 𝒮 ν Q hC) GlobalTheory.T.eventually_constructedPoint_hostSize_numerical).mono ?_
  intro κ K _ H β hq c b hl
  obtain ⟨p, b', hpin, heq⟩ := hl
  have hl' : linkOf (_root_.GlobalTheory.PlugPt.pinnedPointOfReading ν) K β c b.pt :=
    ⟨p, b'.pt, hpin, congrArg (fun y : (Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.Ind.PointSummands D O c) =>
      (⟨y.1, y.2.1, y.2.2.pt⟩ : Σ (D : D7) (O : Obj D), BdPt D O c)) heq⟩
  have ht : TiesB β.D β.O c b.pt := H.1 β hq c b.pt hl'
  have hs : FieldSmall β.D β.O.L := ((H.2 β).2 _ ht.1.tied.field).2.2
  have hw : SingleIndexPlacesAreTwisted b.pt := fun w hw => ((b.muDef 0 0).2.2.2 w).2 hw
  exact ⟨ht, ⟨hs, (GlobalTheory.T.pathCoreConditions_of_intrinsicConditions β.D β.O c b.pt ht hs).2.2.1⟩, GlobalTheory.PlugPt.more_of_tiesB β.D β.O c b.pt ht hs hw⟩
end GlobalTheory.PlugPt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiesOfTiesB

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
theorem ties_of_tiesB_alt : ∀ (D : D7) (O : GlobalTheory.EX.OB.Obj D) (c : ℝ) (b : BdPt D O c), TiesB D O c b →
    GlobalTheory.FinalJoin2.FieldSmall D O.L → b.RealisedCondition → GlobalTheory.EX.DQ.TwAllAt D O.ex.nch O.ex.xd → b.CompatibilityConditions := by
  intro D O c b h hF hR htw
  obtain ⟨hc, hpb, -, hL, hD⟩ := GlobalTheory.T.pathCoreConditions_of_intrinsicConditions D O c b h hF
  obtain ⟨hT, hRay⟩ := h
  exact
    { real := hR, core := hc, pb := hpb, types := hT.types, series := hT.series, level := hL, data := hD,
      psiVal := hT.psiVal, ray := hT.small.ray, roots := hT.small.roots, rayQ := hRay, twist := htw }
end GlobalTheory.PlugPt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTies

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.GeoTies

theorem linked_ties_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  intro hRF hL N S Γ hN hDiv
  have hE : _root_.GlobalTheory.PlugPt.HasExponent' N := (_root_.GlobalTheory.ExpTiesOfLayer.hasExp_of_layer_alt hL).2 N fun K B f T w Z Wt p0 t nch n xd c h =>
    (hN K B f T w Z Wt p0 t nch n xd c h).map Prod.fst
  let ν := _root_.GlobalTheory.PlugPt.ExtensionReading.of RX hE (SXE S) (OX Γ)
  have hRow := _root_.GlobalTheory.PlugPt.rowE_part_ties_alt hRF hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s ν (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (GlobalTheory.Plug.coreCondition_RX _ rfl)
  have hlink : ∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) K β c b → ∀ t : b.Comparison₂,
      linkOf (𝒮 := (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (Bd := _root_.GlobalTheory.Fc.Ind.PointSummands) (fun K q c b => _root_.GlobalTheory.PlugPt.pinnedPointOfReading ν K q c b.pt) K β c (b.part t) := by
    intro K β c b hl t
    obtain ⟨q, b', ⟨w⟩, e⟩ := hl
    have key : ∀ (x y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c), x = y → ∀ t : x.2.2.Comparison₂, ∃ t' : y.2.2.Comparison₂,
        (⟨x.1, x.2.1, x.2.2.part t⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.Ind.PointSummands D O c) = ⟨y.1, y.2.1, y.2.2.part t'⟩ := by
      rintro x _ rfl t
      exact ⟨t, rfl⟩
    obtain ⟨t', e'⟩ := key ⟨β.D, β.O, b⟩ _ e t
    exact ⟨q, b'.part t', _root_.GlobalTheory.T.exponent_reading_of_hasExp_bundle hL N S Γ hE K q c b' w t', e'⟩
  have hB : RowE (sAnd (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) GlobalTheory.PlugPt.RayPosition) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ))
      (fun _ D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) :=
    EvP.mono (fun _ K _ H β hq c b hl t => H β hq c (b.part t) (hlink K β c b hl t)) hRow
  have hR2 : _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) :=
    ⟨GlobalTheory.PlugPt.RayPosition, GlobalTheory.Plug.largeBaseProperty_rayProperty hRF KPx _, RowE.row hB⟩
  obtain ⟨R, hR, hrow⟩ := RowL.and (KP := KPx) (Q := IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s) (Q' := IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s)
    (Lk := _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)) (H := AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition) hDiv hR2
  refine ⟨R, hR, hrow.imp fun 𝒜 σ s H => ?_⟩
  intro eps Fm hc x hx i
  obtain ⟨κ, -, -, hs⟩ := s Fm hc
  refine Built.ind (R := fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => _root_.GlobalTheory.Fc.R1.DivisorBundleCondition D O c b → (∀ t : b.Comparison₂,
      GlobalTheory.PlugPt.TiesB D O c (b.part t).pt ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) → ∀ t : b.Comparison₂,
      _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧
        GlobalTheory.BigOn.More (b.part t).pt) ?_ (hs x hx i).1 (H.1 Fm hc x hx i) (H.2 Fm hc x hx i)
  intro K β c b _ _ hl hdv hT
  have htw : DQ.TwAllAt β.D β.O.ex.nch β.O.ex.xd := twAll_pt β
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have key : ∀ y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c, y = ⟨q.w.D q.Z, q.O, b'⟩ →
      DQ.TwAllAt y.1 y.2.1.ex.nch y.2.1.ex.xd → _root_.GlobalTheory.Fc.R1.DivisorBundleCondition y.1 y.2.1 c y.2.2 → (∀ t : y.2.2.Comparison₂,
        GlobalTheory.PlugPt.TiesB y.1 y.2.1 c (y.2.2.part t).pt ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt) →
      ∀ t : y.2.2.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands y.1 y.2.1 c (y.2.2.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (y.2.2.part t).pt ∧
        (y.2.2.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied y.1 y.2.1.L ∧ GlobalTheory.BigOn.More (y.2.2.part t).pt := by
    rintro _ rfl htw hdv hT t
    obtain ⟨hTB, hRec, hMore⟩ := hT t
    have hcs := _root_.GlobalTheory.T.class_sum_divisibility_of_extensionWithLaw hL N S Γ hN K q c b' w t
    refine ⟨hcs.1, hcs.2 (_root_.GlobalTheory.Fc.FourBoundsAtBundles.p_div_of_div3g _ hdv), ?_, hRec, hMore⟩
    exact _root_.GlobalTheory.PlugPt.ties_of_tiesB_alt _ _ c _ hTB hRec.1 (_root_.GlobalTheory.Fc.Ind.pt_realised_and_pb_eq _ _ c _).1 htw
  exact key ⟨β.D, β.O, b⟩ e htw hdv hT
end GlobalTheory.GeoTies
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedTiesStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.class_sum_divisor_all_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.R1.SlotDivisorCondition → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) fun Q L => Row Q L (AtAll fun D O c (b : _root_.GlobalTheory.Fc.BundleCondition D O c) => ∀ t : b.Comparison₂, _root_.GlobalTheory.Fc.Ind.IotaPointSummands D O c (b.part t) ∧ GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.CompatibilityConditions ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt) := by
  first | exact @_root_.GlobalTheory.GeoTies.linked_ties_alt | exact _root_.GlobalTheory.GeoTies.linked_ties_alt | (intros; apply _root_.GlobalTheory.GeoTies.linked_ties_alt <;> assumption)
end
end
end
