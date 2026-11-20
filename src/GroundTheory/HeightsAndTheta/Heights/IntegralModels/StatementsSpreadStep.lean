import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

def SpreadStep.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)}))).Modules) (W₁ W₂ : X.Opens),
    SpreadsOn f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) E W₁ → SpreadsOn f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) E W₂ →
    ∃ W : X.Opens, baseChangeMap f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) ⁻¹ᵁ W₁ ⊔ baseChangeMap f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) ⁻¹ᵁ W₂ ≤
        baseChangeMap f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) ⁻¹ᵁ W ∧ SpreadsOn f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) E W

end

end GroundTheory.Heights₂.Heights.Model
