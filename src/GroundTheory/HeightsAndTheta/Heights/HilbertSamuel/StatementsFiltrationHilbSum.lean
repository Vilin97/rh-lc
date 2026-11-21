module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u v

def FiltrationHilbSum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) M] [Module F M]
    [IsScalarTower F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    ∀ (n : ℕ) (N : Fin (n + 1) → Submodule (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) M) (x : Fin n → M) (c : Fin n → K → ℤ)
      (q : Fin n → Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)),
      N 0 = ⊥ → N (Fin.last n) = ⊤ →
      (∀ j : Fin n, x j ∈ piece (c j) ∧
        N j.succ = N j.castSucc ⊔ Submodule.span (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) {x j} ∧
        ∀ s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι, s • x j ∈ N j.castSucc ↔ s ∈ q j) →
      ∀ m : K → ℤ, (Module.finrank F (piece m) : ℤ) = ∑ j, hilbFn (q j) (m - c j)

section Examples

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

end Examples

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
