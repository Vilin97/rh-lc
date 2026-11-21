module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpVerticalFibre
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {K : Type} [DecidableEq K] {ι : K → Type} {J : Type}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

open Classical in

def specialRelDeg (W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J))) : ℕ :=
  if h : (specialIdeal W').IsPrime then
    haveI := h
    FieldNumbers.relDeg Function.Embedding.some (specialIdeal W')
  else 0

end Objects

section Lemmas

def BlowUpFibreDegree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W → ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ) ≠ 0 →
      (open Classical in
        ∑ᶠ W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)),
          if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
            ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W' : ℤ) * (specialRelDeg W' : ℤ)
          else 0) =
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
