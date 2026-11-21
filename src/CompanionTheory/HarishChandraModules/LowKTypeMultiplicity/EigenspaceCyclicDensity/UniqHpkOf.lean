module

public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.PeriodIntegrals.UpqRep

@[expose] public section

open Matrix

noncomputable section

namespace CompanionTheory.D.LK

def DSUniqP : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.QuantumDeterminants.IsHCParam lam → PI.UpqRep.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ PI.UpqRep.UJset ε, ∀ x, U (σ g x) = σ' g (U x)

end CompanionTheory.D.LK
