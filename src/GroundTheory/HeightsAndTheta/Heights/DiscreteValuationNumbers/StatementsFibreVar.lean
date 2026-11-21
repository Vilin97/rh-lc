module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def FibreVarieties.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d →
      (IsMultiProjPrime (genFib P) ∧
        ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) ∧
      ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C ϖ)) W : ℤ) ≠ 0 →
        IsMultiProjPrime (specialIdeal W) ∧
          ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
            ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
