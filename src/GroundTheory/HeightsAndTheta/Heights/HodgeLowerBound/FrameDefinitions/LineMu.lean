import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

variable {II hII}

section Frame

variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)

set_option maxHeartbeats 2000000 in

end Frame

section FrameLemmas

variable {c : Unit → Fin 2} {f : Ω} {b : Fin 2 → Fin 2 → Ω}

variable {z : (Σ _ : Unit, Fin 2) → ℂ}

end FrameLemmas

section Norm

variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)

end Norm

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
