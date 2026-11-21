import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrkbLeOneAddSq
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyProjectorSectionLocal
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.LogSumExpBounds.StatementD
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.LatticeRigidity.StatementC
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Set TopologicalSpace
open scoped InnerProductSpace ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma
open Formalism.HermitianLatticeCounting.S7 (decExp)

def DistTri : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), cartanDistance ε (g * k) ≤ cartanDistance ε g + cartanDistance ε k

end Formalism.MainNotions.LeviCoordinates

end
