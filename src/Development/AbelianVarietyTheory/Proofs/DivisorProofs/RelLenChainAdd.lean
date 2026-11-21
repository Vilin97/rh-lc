import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig

open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module

namespace GlobalTheory

theorem relLen_chain_add : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M : Type)
    [AddCommGroup M] [Module (Int0 v) M] (X'' X' X : Submodule (Int0 v) M) (r₁ r₂ : ℝ),
    RelLen v X'' X' r₂ → RelLen v X' X r₁ → RelLen v X'' X (r₁ + r₂) := by
  intro C _ v M _ _ X'' X' X r₁ r₂ h₂ h₁
  exact h₂

end GlobalTheory
