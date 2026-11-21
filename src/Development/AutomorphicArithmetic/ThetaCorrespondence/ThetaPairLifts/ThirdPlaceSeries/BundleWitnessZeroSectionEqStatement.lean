module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.CarriedPlMap
public import Formalism.LocalToGlobal.SelSide
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Formalism.LocalToGlobal.Divisibility.ColPins
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
public import Formalism.LocalToGlobal.Divisibility.TupUsed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqClosedContentNumericalDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BundleWitnessZeroSectionEq
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bWit_zsc_F0_heq_F0K_local_of_sc_eq : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b), q.O.L.sc = K.s → HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  first | exact @_root_.GlobalTheory.Mem.Top.Bl.bWit_zsc_F0_heq_F0K_of_sc_eq | exact _root_.GlobalTheory.Mem.Top.Bl.bWit_zsc_F0_heq_F0K_of_sc_eq | (intros; apply _root_.GlobalTheory.Mem.Top.Bl.bWit_zsc_F0_heq_F0K_of_sc_eq <;> assumption)
end
