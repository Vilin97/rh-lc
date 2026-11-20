import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SpanTwoIsPrimeRelevant
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

def divisorIdeal (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) :=
  (P ⊔ Ideal.span {f}).colon {g}

end Defs

section Lemmas

def VNumCut.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (G : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), G.IsPrime → IsMultiHomogIdeal G → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G →
    ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) (c : K → ℕ), IsMultiHomog s c → s ∉ G →
    ∀ bs : Fin n → K → ℤ,
      vNum G (Matrix.vecCons (fun k => (c k : ℤ)) bs) = cycEval (fun U => vNum U bs) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle G s) W : ℤ)))

def DivisorIdealCycle.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] [DecidableEq K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) (f g u v : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι),
    P.IsPrime → W.IsPrime → P ≤ W → g ∉ P →
    (∀ U : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι), U.IsPrime → W ≤ U → IsRelevant U →
      ∃ u' v' : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι, u' ∉ U ∧ u' * f - v' * g ∈ P) →
    u ∉ W → v ∉ W → u * f - v * g ∈ P →
    ratDiv W v u = idealCycle (W ⊔ divisorIdeal P f g)

def VertCutEff.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (n : ℕ), IsModelOver P (n + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), x ∉ P → W ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
      IsRelevant W → IsMultiHomogIdeal W → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W → ratDiv P f g W = 0 →
    ∀ L : Fin n → K → ℤ,
      vNum W (Matrix.vecCons b L) =
        cycEval (fun U => vNum U L) (idealCycle (W ⊔ divisorIdeal P f g))

def LeftExpansion.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ G, (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G → ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ,
      cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
        cycEval (fun U => vNum U L) (fun U => cycEval (fun G => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle G s) U : ℤ)) (ratDiv P f g))

open Classical in

def RightExpansion.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G → ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ,
      cycEval (fun W => if (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W then vNum W (Matrix.vecCons b L)
          else cycEval (fun G => vNum G L) (ratDiv W f g)) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ))) =
        cycEval (fun U => vNum U L)
          (fun U => cycEval (fun W => idealCycle (W ⊔ divisorIdeal P f g) U) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ))))

def LocalCoefficient.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G → ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) ≠ 0 → ratDiv P f g G = 0) →
    ∀ U : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
      (U.IsPrime → IsMultiHomogIdeal U → IsRelevant U → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ U →
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι ⧸ U)) →
      cycEval (fun G => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle G s) U : ℤ)) (ratDiv P f g) =
        cycEval (fun W => idealCycle (W ⊔ divisorIdeal P f g) U) ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ)))

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
