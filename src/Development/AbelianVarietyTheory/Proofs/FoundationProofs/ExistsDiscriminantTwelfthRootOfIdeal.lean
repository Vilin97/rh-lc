import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace GlobalTheory.Glob.IntegralWittCoefficients

theorem isCurveIdeal_top (D : D7) : IsCurveIdeal D ⊤ :=
  ⟨top_ne_bot, by simp⟩

end GlobalTheory.Glob.IntegralWittCoefficients
