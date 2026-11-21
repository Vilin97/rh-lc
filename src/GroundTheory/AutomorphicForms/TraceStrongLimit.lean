import Mathlib
import GroundTheory.AutomorphicForms.TraceNormComp

namespace GroundTheory.Automorphic

open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section FinProj

variable {ι : Type*} [Fintype ι]

def finProj (u : ι → H) : H →L[ℂ] H := ∑ i, rankOne ℂ (u i) (u i)

variable {u : ι → H}

end FinProj

section Limits

variable [CompleteSpace H]

end Limits

end

end GroundTheory.Automorphic
