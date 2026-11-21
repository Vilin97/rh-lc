module

public import Mathlib
public import GroundTheory.AutomorphicForms.HarishChandraCentre.ConstantCoeffRhoOneCanonMonomial
public import Formalism.PeriodIntegrals.IsLowUnitH
public import Formalism.PeriodIntegrals.DSInfCharCap

@[expose] public section

open GroundTheory.Automorphic.HarishChandra Finset

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.CompanionTheory.DS

variable {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]

section Unitary

open scoped InnerProductSpace

variable {Y : Type} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Unitary

def DSUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    PI.UpqRep.IsHCParam lam → PI.UpqRep.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ' → PI.UpqRep.IsEquiv ε σ' σ

end GlobalTheory.CompanionTheory.DS
