import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreSemilocalCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Objects

variable {A : Type*} [CommRing A] (L : Type*) [Field L] [Algebra A L]

def blowUpColon (I : Ideal A) : Submodule A L :=
  ⨆ n : ℕ, (Submodule.map (Algebra.linearMap A L) I) ^ n / (Submodule.map (Algebra.linearMap A L) I) ^ n

end Objects

section Lemmas

def BlowUpOverLocInChart.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (J : Type)
    (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [P.IsPrime], IsMultiHomogIdeal P → W.IsPrime → P ≤ W → IsRelevant W →
    ∀ (N : K → ℕ) (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι), (∀ j, IsMultiHomog (u j) N) → ∀ j, u j ∉ P →
      blowUpOverLoc P W u ≤ Subring.closure ((homLocRing P W : Set (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P))) ∪
        Set.range fun k =>
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) (Ideal.Quotient.mk P (u k)) /
            algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) (Ideal.Quotient.mk P (u j)))

def ChartsInColon.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (L : Type u) [Field L] [Algebra A L] (J : Type) [Fintype J] (a : J → A) (f : L),
    (∀ j, algebraMap A L (a j) ≠ 0 →
      f ∈ Algebra.adjoin A (Set.range fun k => algebraMap A L (a k) / algebraMap A L (a j))) →
    f ∈ blowUpColon L (Ideal.span (Set.range a))

def BlowUpColonFinite.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (L : Type u) [Field L]
    [Algebra A L], Function.Injective (algebraMap A L) → ringKrullDim A = 1 →
    ∀ I : Ideal A, I ≠ ⊥ → (blowUpColon L I).FG

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
