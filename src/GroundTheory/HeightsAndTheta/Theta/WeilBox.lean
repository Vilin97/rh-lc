module

public import Mathlib
public import GroundTheory.LocalFields.LocalFourier
public import GroundTheory.AutomorphicForms.MeasuresModulus

@[expose] public section

noncomputable section

namespace GroundTheory.Heights₂.Theta

open GroundTheory.LocalField ValuativeRel MeasureTheory Measure Topology Filter Matrix
open scoped WithZero NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {ι : Type*} [Fintype ι]

section Boxes


variable [MeasurableSpace F] [BorelSpace F]

end Boxes

section SchwartzBruhat


variable (F ι) in
def schwartzBruhatPi : Submodule ℂ ((ι → F) → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.smul_left (f := fun _ => c)⟩

end SchwartzBruhat

section Fourier

variable [MeasurableSpace F] [BorelSpace F]


variable {ψ : AddChar F Circle}

variable (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ

include hψ1

end Fourier

end GroundTheory.Heights₂.Theta
