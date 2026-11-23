module

public import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VwinOfRow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.Development
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.WeightOneGeometricRealization
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TLiftK
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EveryCharacterOfLiteratureOfVWin

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GaloisRepresentationsOfThetaLift

section

@[expose] public section

namespace UpperTheory.Gal.Int

theorem galoisRepresentations_of_thetaLift (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0b recT := galoisLocalGlobalStrong_of_geometry_lift UpperTheory.Gal.Int.Geo.geoOne_holds up

end UpperTheory.Gal.Int
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.RowSrc

section

@[expose] public section

namespace UpperTheory.Gal.Int

theorem galoisLocalGlobalStrong_recParameter : UpperTheory.GalStar.Row0b recT := galoisRepresentations_of_thetaLift UpperTheory.TP.K.tLiftK

end UpperTheory.Gal.Int
end
end

-- Source module: Development.AutomorphicArithmetic.CharacterBoxes.MainConclusion

section

@[expose] public section

theorem UpperTheory.FinalTheorems.everyCharacter_of_row
    (h : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    UpperTheory.EveryCharacter :=
  UpperTheory.LiteratureTheorems.every_character_of_literature_of_vWin
    { caraianiLocalGlobalDual := h
      localLanglandsExists := UpperTheory.Zero.LLC.recTExists
      galoisRepOfPolarizedPairLit := h }
    (UpperTheory.One.vwin_of_row h)

theorem UpperTheory.FinalTheorems.everyCharacter : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter_of_row UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter
end
end
