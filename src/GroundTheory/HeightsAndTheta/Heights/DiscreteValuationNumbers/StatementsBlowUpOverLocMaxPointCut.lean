import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocMaxCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocMaxCentre.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ (𝔫 : Ideal (blowUpOverLoc P W u)) (h𝔫 : 𝔫.IsMaximal),
        ∃ W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)),
          W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ IsRelevant W' ∧ blowUpOf P u ≤ W' ∧
            W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W ∧
          ∃ h : blowUpOverLoc P W u ≤ blowUpLocRing P u W',
            letI := (Subring.inclusion h).toAlgebra
            haveI := h𝔫.isPrime
            IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫

def BlowUpOverLocFibreMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
    ∀ W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), W'.IsPrime → IsMultiHomogIdeal W' → IsRelevant W' →
      blowUpOf P u ≤ W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes

def BlowUpOverLocPointDeg.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ) (hP : IsModelOver P n),
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W →
      haveI := hP.multiProj.isPrime
      ∀ W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes →
        IsRelevant W' → W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
        ∃ (h : blowUpOverLoc P W u ≤ blowUpLocRing P u W') (𝔫 : Ideal (blowUpOverLoc P W u))
          (h𝔫 : 𝔫.IsMaximal),
          (letI := (Subring.inclusion h).toAlgebra
           haveI := h𝔫.isPrime
           IsLocalization.AtPrime (blowUpLocRing P u W') 𝔫) ∧
          𝔫.inertiaDeg (homLocRing P W) = specialRelDeg W'

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
