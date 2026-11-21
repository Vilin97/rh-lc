import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSympl
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
import Mathlib
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

def Gf (ψ : AddChar (AF D.host.F) ℂ) (L : (Fin k → ℝ) →+ WO S T) (f : WO S T → ℂ) (x : WO S T) :
    (Fin k → ℝ) → ℂ := fun t => heisO ψ S T (L t) f x

section Bound

variable {ψ : AddChar (AF D.host.F) ℂ} {Λ : Ainf D.host.F →+ ℂ} (hΛ : Continuous Λ)
  (hψΛ : ∀ z : AF D.host.F, z.2 = 0 → ψ z = Complex.exp (Λ z.1))
  {L : (Fin k → ℝ) →+ WO S T} (hL : IsRealFrame L)

include hΛ hψΛ hL in

include hΛ hψΛ hL in

end Bound

end Formalism.IndefR.Eqv

end
