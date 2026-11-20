import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

noncomputable section

def ZLocDenominators.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (p : Nat.Primes) (U : X.Opens), IsAffineOpen U →
    ∀ b : Γ(baseChange f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})), baseChangeMap f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) ⁻¹ᵁ U),
      ∃ N : ℕ, 0 < N ∧ ¬ (p : ℕ) ∣ N ∧ ∃ c : Γ(X, U), (baseChangeMap f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)}))).app U c = N • b

end

end GroundTheory.Heights₂.Heights.Model
