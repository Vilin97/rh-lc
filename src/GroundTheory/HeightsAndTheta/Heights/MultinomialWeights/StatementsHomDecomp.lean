import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.StatementsEnd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial

def HomDecompExists.Statement : Prop :=
  ∀ (d : IndexData) (F : MvPolynomial (Fin d.f × Fin d.N) ℚ), F.IsHomogeneous (d.D + 1) →
    ∃ Q : ℕ → Fin d.f → MvPolynomial (Fin d.f × Fin d.N) ℚ, IsHomDecomp d F Q

end GroundTheory.Heights₂.Heights.TheoremB
