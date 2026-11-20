import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegreeCut
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def HomLocRingMem.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [P.IsPrime], W.IsPrime → P ≤ W →
    ∀ z : FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P), z ∈ homLocRing P W ↔
      ∃ (b : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι), IsMultiHomog f b ∧ IsMultiHomog g b ∧ g ∉ W ∧
        z = algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) (Ideal.Quotient.mk P g)

def HomLocRingIsLocal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type)
    (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [P.IsPrime], W.IsPrime → P ≤ W →
    IsLocalRing (homLocRing P W) ∧
      ∀ (b : K → ℕ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι), IsMultiHomog f b → IsMultiHomog g b → g ∉ W →
        ∀ hz : algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) (Ideal.Quotient.mk P f) /
            algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P) (FractionRing (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ P)) (Ideal.Quotient.mk P g) ∈
              homLocRing P W,
          IsUnit (⟨_, hz⟩ : homLocRing P W) ↔ f ∉ W

def HomLocRingNoetherian.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      IsNoetherianRing (homLocRing P W)

def HomLocRingDimLe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) [P.IsPrime],
    IsMultiHomogIdeal P → W.IsPrime → IsRelevant W → P ≤ W →
      ringKrullDim (homLocRing P W) ≤ ((W.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
