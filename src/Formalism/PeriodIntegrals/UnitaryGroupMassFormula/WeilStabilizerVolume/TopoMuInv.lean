import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Formalism.PeriodIntegrals.WeilQuotMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq

noncomputable section

namespace PI.VolStabW.TopoMuInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

end PI.VolStabW.TopoMuInv

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

end PI.VolStabW
