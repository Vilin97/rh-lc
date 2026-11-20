import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

variable {X : Scheme.{0}}

def SpreadsOn (f : X ⟶ SpecZ) (R : Type) [CommRing R] (E : (baseChange f R).Modules)
    (W : X.Opens) : Prop :=
  ∃ E' : (W : Scheme.{0}).Modules, IsVectorBundle E' ∧
    Nonempty ((Scheme.Modules.pullback (baseChangeMap f R ∣_ W)).obj E' ≅
      (Scheme.Modules.pullback (baseChangeMap f R ⁻¹ᵁ W).ι).obj E)

def SpreadLocal.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) (p : Nat.Primes) (E : (baseChange f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)}))).Modules),
    IsVectorBundle E → ∀ x : baseChange f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})),
      ∃ W : X.Opens, x ∈ baseChangeMap f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) ⁻¹ᵁ W ∧ SpreadsOn f (Localization.AtPrime (Ideal.span {((p : ℕ) : ℤ)})) E W

def specZLocToBaseChange :
    Spec (CommRingCat.of (ZLoc ⟨2, Nat.prime_two⟩)) ⟶ baseChange (𝟙 SpecZ) (ZLoc ⟨2, Nat.prime_two⟩) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (Int.castRingHom _))) (𝟙 _) (by simp)

end

end GroundTheory.Heights₂.Heights.Model
