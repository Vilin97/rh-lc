module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpHorizontalSat.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W →
      ∃ j, ∀ j', ∃ v w : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ) ≠ 0 →
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∉ W →
      ∀ F : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J), F ∈ W ↔ ∃ s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, s ∉ W.comap (liftForm (ι := ι) (J := J) (R := O)) ∧
        (liftForm (ι := ι) (J := J) (R := O)) s * F ∈ blowUpOf P u ⊔ Ideal.map (liftForm (ι := ι) (J := J) (R := O)) (W.comap (liftForm (ι := ι) (J := J) (R := O)))

def BlowUpHorizontalMult.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W →
      ∃ j, ∀ j', ∃ v w : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ) ≠ 0 →
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∉ W →
      ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) (W.comap (liftForm (ι := ι) (J := J) (R := O))) : ℤ) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ)

def BlowUpHorizontalLift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W →
      ∃ j, ∀ j', ∃ v w : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) W : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W →
      ∃ W' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W' : ℤ) ≠ 0 ∧
        (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∉ W' ∧ W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W

def BlowUpHorizontalStrict.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    (∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W →
      ∃ j, ∀ j', ∃ v w : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, v ∉ W ∧ v * u j' - w * u j ∈ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)), ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm x)) W : ℤ) ≠ 0 →
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) ∉ W →
      (∃ j, u j ∉ W.comap (liftForm (ι := ι) (J := J) (R := O))) → W = blowUpOf (W.comap (liftForm (ι := ι) (J := J) (R := O))) u

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
