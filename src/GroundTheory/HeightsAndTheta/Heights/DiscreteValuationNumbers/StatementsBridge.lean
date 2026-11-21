module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def VocabMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (a : K → ℕ),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a ↔ IsMultiHomog s a

def VocabMultiHomogIdeal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)),
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P ↔ IsMultiHomogIdeal P

def VocabDivCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)),
    ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) : ℤ) = ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ)

def IntNumPoint.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (i : ∀ k, ι k), IsMultiProjPrime V →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ V) = ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ k, (X ⟨k, i k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) ∉ V) →
    intNum F V (![] : Fin 0 → K → ℤ) = ReciprocityTheory.ChartRestriction.G.AI.I1.ptDeg V i

def IntNumRatSection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime V →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ V) = ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (L : Fin n → K → ℤ) (A : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι) (α β : K → ℕ),
      IsMultiHomog f α → IsMultiHomog g β → f ∉ V → g ∉ V → (∀ k, (α k : ℤ) - β k = A k) →
      intNum F V (Fin.snoc (α := fun _ => K → ℤ) L A) =
        cycEval (fun W => intNum F W L) (ratDiv V f g)

def IntNumIsFieldIntersection.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)],
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection (F := F) (ι := ι) (fun V _ L => intNum F V L)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
