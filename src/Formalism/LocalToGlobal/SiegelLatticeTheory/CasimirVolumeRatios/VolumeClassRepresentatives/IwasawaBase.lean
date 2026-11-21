import Formalism.PeriodIntegrals.LatCountG
import Formalism.HarderNarasimhan.StatementPl
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
import Formalism.LogSumExpBounds.StatementD
import Formalism.LatticeRigidity.HeightMinimum.PackingCountGeometricMean
import Mathlib
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.LatticeRigidity.StatementC
import Formalism.LatticeRigidity.HeightMinimum.SqrtAbsNormLeProd
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative

noncomputable section

namespace Formalism.L2.S.S7.IwasawaBase

open MeasureTheory NumberField
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups

variable (I : AutInst)

theorem muA_right (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] : (I.muA μf).IsMulRightInvariant := by
  have : μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds I μf
  exact rr_muA_right I μf

end Formalism.L2.S.S7.IwasawaBase

end
