import Mathlib
import GroundTheory.PAdicHodge.FieldOfNormsRam
import GroundTheory.PAdicHodge.FieldOfNormsTower
import GroundTheory.LocalFields.Examples
import GroundTheory.LocalFields.ExamplesCharZero
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open GroundTheory.LocalField ValuativeRel Filter Topology IntermediateField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsGalois K Ω]

section GaloisAPF

variable {L : IntermediateField K Ω} [IsGalois K L]

variable (hL : IsAPF K Ω L)
include hL

end GaloisAPF

section Tower

variable {L : IntermediateField K Ω} [IsGalois K L] (hL : IsAPF K Ω L)
include hL

end Tower

section Construction

variable {L : IntermediateField K Ω} [IsGalois K L]

structure APFData (L : IntermediateField K Ω) where
  apf : IsAPF K Ω L
  c : ℝ
  c_pos : 0 < c
  u₀ : ℝ
  one_le_u₀ : 1 ≤ u₀
  le_psi : ∀ u, u₀ ≤ u → c * apfIndex K Ω L u ≤ apfPsi K Ω L u

namespace APFData

variable (d : APFData L)

def u (n : ℕ) : ℝ := d.u₀ + n * (d.c / 2)

open Classical in

end APFData

end Construction

omit [IsGalois K Ω] in

omit [IsGalois K Ω] in

namespace APFData

variable {L : IntermediateField K Ω} [IsGalois K L] (d : APFData L)

omit [IsGalois K Ω] in

end APFData

end GroundTheory.PAdicHodge
