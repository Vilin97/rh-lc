module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsPointHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Module Matrix
open scoped ComplexOrder

noncomputable section

section Embedding

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

end Embedding

end

end GroundTheory.Heights₂.Heights
