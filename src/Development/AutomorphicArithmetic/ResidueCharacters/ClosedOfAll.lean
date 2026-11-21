import Development.AutomorphicArithmetic.ResidueCharacters.RowThreeC
import Development.AutomorphicArithmetic.ResidueCharacters.NumCost
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersFamilyConstStatement
import Mathlib
import Development.AutomorphicArithmetic.ResidueCharacters.ConclusionSplitOfHub
import Development.AutomorphicArithmetic.ResidueCharacters.TwoDecl
import Development.AutomorphicArithmetic.ResidueCharacters.LenUnitInvariantsLe
import Development.AutomorphicArithmetic.ResidueCharacters.LocAll
import Development.AutomorphicArithmetic.ResidueCharacters.NumRow
import Development.AutomorphicArithmetic.ResidueCharacters.ThreeHost
import Development.AutomorphicArithmetic.ResidueCharacters.PlaceTypeConj
import Development.AutomorphicArithmetic.CyclotomicBounds.NotInert
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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

theorem closed_of_all (𝒞 : FamClass) {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), P Fm CH) :
    Closed 𝒞 P :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => h Fm CH⟩⟩

end UpperTheory.N
