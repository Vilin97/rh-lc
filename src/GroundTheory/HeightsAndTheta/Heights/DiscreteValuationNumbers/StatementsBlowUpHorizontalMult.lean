module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpHorizontalMinimal.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W →
      ∃ j, ∀ j', ∃ v w : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ) ≠ 0 →
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∉ W →
      W.comap (liftForm (ι := ι) (J := J) (R := O)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes

def BlowUpHorizontalChartLength.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W →
      ∃ j, ∀ j', ∃ v w : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ) ≠ 0 →
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∉ W →
      ∀ hW : W.IsPrime,
      haveI := hW
      multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) W =
        Module.length
          (Localization.AtPrime ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
            (Polynomial.C : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι →+* Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι))))
          (LocalizedModule ((W.comap (liftForm (ι := ι) (J := J) (R := O))).map
              (Polynomial.C : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι →+* Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι))).primeCompl
            (Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ⧸
              (P ⊔ Ideal.span {x}).map (Polynomial.C : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι →+* Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι))))

def PolynomialLocalizedLength.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (q : Ideal R) [q.IsPrime] (I : Ideal R),
    Module.length (Localization.AtPrime (q.map (Polynomial.C : R →+* Polynomial R)))
        (LocalizedModule (q.map (Polynomial.C : R →+* Polynomial R)).primeCompl
          (Polynomial R ⧸ I.map (Polynomial.C : R →+* Polynomial R))) =
      Module.length (Localization.AtPrime q) (LocalizedModule q.primeCompl (R ⧸ I))

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
