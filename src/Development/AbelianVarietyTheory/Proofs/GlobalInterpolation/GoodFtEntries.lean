import Mathlib
import Development.AutomorphicArithmetic.CharacterBoxes.ExS
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
import Formalism.LocalToGlobal.FiniteTOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Formalism.LocalToGlobal.CarriedPlMap
import Formalism.LocalToGlobal.SelSide
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
import Formalism.LocalToGlobal.Divisibility.ColPins
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Formalism.LocalToGlobal.IndefiniteReal.NonzeroIndexPlaceIndepConstants
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OExt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTruthOfLabelTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConstructedSpectralObjectsIrreducibilityConditioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsTerAlt

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM

namespace GlobalTheory.Fc.LabLinked

def Ties (D : D7) : Prop :=
  ∃ (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : Formalism.L2.SG.RowDict.GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X),
    Formalism.MainNotions.S.AutTie D X.B X.pl ∧ Formalism.L2.SG.RowDict.RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι

set_option maxHeartbeats 2000000 in

section Rows

open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.NX

set_option maxHeartbeats 1000000 in

end Rows

theorem lab_of_rows {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
  fun k => ⟨(t.grp.teich k).symm, t.grp.ser k⟩

set_option maxHeartbeats 1000000 in

end GlobalTheory.Fc.LabLinked
