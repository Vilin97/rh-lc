module

public import Mathlib
public import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open WittVector Filter Topology

namespace GroundTheory.PAdicHodge

section Coordinates

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

variable [CharP R p]

end Coordinates

namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

variable (K p) in

variable (K p) in

omit hp [IsPerfectoidField K p] in

theorem isAdicComplete_p : IsAdicComplete (Ideal.span {(p : AInf K p)}) (AInf K p) :=
  inferInstance

omit hp [IsPerfectoidField K p] in

end AInf

end GroundTheory.PAdicHodge
