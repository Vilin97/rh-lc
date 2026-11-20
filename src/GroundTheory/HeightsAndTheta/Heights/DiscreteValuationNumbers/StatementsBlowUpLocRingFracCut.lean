import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFrac
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocFamilyFinite.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      {Q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι J)) | Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W}.Finite

def MultiHomogPrimeAvoid.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (S : Set (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι))), S.Finite →
    (∀ Q ∈ S, Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q) →
    ∃ (e : K → ℕ) (L : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι), IsMultiHomog L e ∧ (∀ k, 1 ≤ e k) ∧ ∀ Q ∈ S, L ∉ Q

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
