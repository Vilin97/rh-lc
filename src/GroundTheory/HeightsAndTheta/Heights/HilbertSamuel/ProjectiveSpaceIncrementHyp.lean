module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] (ι : K → Type*) {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) M] [Module F M]
  [IsScalarTower F (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) M]


variable {ι}

end Objects

section Support

variable {S : Type*} [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]

end Support

section Cycle

variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
variable (M : Type*) [AddCommGroup M] [Module (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) M]

end Cycle

section Statements

def HilbertIncrement.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (b : K) (i : ι b),
    IsMultiProjPrime q → ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    1 ≤ d → (X ⟨b, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ q →
    (∀ a : K → ℤ, hilbFn q a - hilbFn q (a - Pi.single b 1) =
        hilbFn (q ⊔ Ideal.span {(X ⟨b, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)}) a) ∧
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiProjPrime W → q ⊔ Ideal.span {(X ⟨b, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)} ≤ W →
      ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ W) ≤ ((d - 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

end Statements

section Examples

variable {K : Type*} [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
