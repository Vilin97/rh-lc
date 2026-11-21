module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterUnitary
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc

@[expose] public section

open ValuativeRel
open scoped Matrix Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_unitary : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ∀ x : k, ‖ψ0 x‖ = 1 := by
  first | exact @GlobalTheory.addChar_norm_eq_one | exact GlobalTheory.addChar_norm_eq_one | (intros; apply GlobalTheory.addChar_norm_eq_one <;> assumption)
