import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensExTop

noncomputable section

namespace HcInf

open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal

section Lie

variable (P Q : ℕ)

instance : BorelSpace (lieU P Q) := ⟨rfl⟩

end Lie

end HcInf
