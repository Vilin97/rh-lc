import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.LatticeRigidity.HeightMinimum.PowFinrankEqZeroOfTracePow
import Mathlib
import Formalism.LogSumExpBounds.StatementD
import Formalism.GelfandTransference.EnergyIdentity
import Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.HarderNarasimhan.ShiftInvariance

open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix

namespace Formalism.HermitianLatticeCounting.P

section Frob
open scoped Matrix.Norms.Frobenius

end Frob

noncomputable def n2 {N : ℕ} (v : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

section FrobG
open scoped Matrix.Norms.Frobenius

end FrobG

open NumberField in

end Formalism.HermitianLatticeCounting.P
