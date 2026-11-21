module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFibreVar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def VerticalComponentFibre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d →
    ∀ (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) (b : K → ℕ), IsMultiHomog f b → f ∉ P →
    ∀ W ∈ (P ⊔ Ideal.span {f}).minimalPrimes, IsRelevant W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W →
      IsMultiProjPrime (specialIdeal W) ∧
        ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
