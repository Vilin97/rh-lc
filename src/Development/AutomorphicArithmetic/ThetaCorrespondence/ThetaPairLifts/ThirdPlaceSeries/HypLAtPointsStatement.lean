import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembers
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.CarriedPlMap
import Formalism.LocalToGlobal.SelSide
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.Divisibility.ColPins
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypLAtPoints
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degHypL_all_linked_good_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (A B : Formalism.MainNotions.Inhab.FC → ℝ), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun κ D O _ _ => GlobalTheory.Core.Deg.HypL D O.L.sc.L (max (A κ.C) (8 * κ.C.CGam)) (max (B κ.C) 40) (κ.C.P.CYL + 1) (1 / 4) 3 (1 / 2) κ.C.CTu) := by
  first | exact @_root_.GlobalTheory.Core.HypAt.hypL_at_points_alt | exact _root_.GlobalTheory.Core.HypAt.hypL_at_points_alt | (intros; apply _root_.GlobalTheory.Core.HypAt.hypL_at_points_alt <;> assumption)
end
