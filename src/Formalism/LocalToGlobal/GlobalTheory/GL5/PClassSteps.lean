import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.AdelicBounds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.LatticeClassesFiniteRefinement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.PosDefOfDefiniteSignatureHolds

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassMass Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

end Gen

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps

end
