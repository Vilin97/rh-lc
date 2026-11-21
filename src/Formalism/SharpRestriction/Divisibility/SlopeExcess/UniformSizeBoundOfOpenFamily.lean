import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.DegreeFormula.PointDegree.FlagDeg
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.FreeFamilyOfLeavesAndAdmissible
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLbud
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.BasicNotions Formalism.MainNotions

theorem top2c2_dlSize (eps : ℝ) (Fm : FamP eps) : J.DlSize Fm := by
  unfold J.DlSize
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx1 i
  obtain ⟨-, -, -, -, -, h, -⟩ := hQD
  exact h

end Formalism.MainNotions.DIV.Proofs
