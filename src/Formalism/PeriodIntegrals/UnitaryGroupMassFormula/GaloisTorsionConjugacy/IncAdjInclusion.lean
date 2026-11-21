import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulDefs

noncomputable section

namespace PI.GalTorsConj.W

open Polynomial

theorem extRho : ExtRho := by
  intro M M₁ h halg ρ
  letI iA : Algebra M M₁ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI hA : Algebra.IsAlgebraic M M₁ := by
    refine ⟨fun x => ?_⟩
    let f : M₁ →ₐ[M] ℂ :=
      { toRingHom := (M₁.val : M₁ →+* ℂ)
        commutes' := fun _ => rfl }
    exact (isAlgebraic_algHom_iff f M₁.val.injective).mp (halg x x.2)
  letI iC : Algebra M ℂ := ρ.toRingHom.toAlgebra
  let φ : M₁ →ₐ[M] ℂ := IsAlgClosed.lift
  refine ⟨{ toRingHom := φ.toRingHom, commutes' := φ.toRingHom.map_rat_algebraMap }, fun x => ?_⟩
  exact φ.commutes x

end PI.GalTorsConj.W

end
