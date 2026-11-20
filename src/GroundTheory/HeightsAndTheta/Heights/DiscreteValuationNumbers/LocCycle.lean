import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivisorIdealBotUniformiser
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]

open Classical in

def locCycle (J W : Ideal R) : ℤ :=
  if h : W ∈ J.minimalPrimes then
    haveI : W.IsPrime := h.1.1
    ((Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J))).toNat : ℤ)
  else 0

end Defs

section Lemmas

def LeftTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c →
    ∀ G U : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ U ∧ P ≤ U) →
      ratDiv P f g G * ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle G s) U : ℤ) = 0

def RightTermSupport.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)), IsMultiHomogIdeal P →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ W U : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
      ¬ (U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ U ∧ P ≤ U) →
      ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W : ℤ) * idealCycle (W ⊔ divisorIdeal P f g) U = 0

def LocalCoeffRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (P U : Ideal R), P.IsPrime → U.IsPrime → P ≤ U →
    (∀ Q₁ Q₂ : Ideal R, Q₁.IsPrime → Q₂.IsPrime → P < Q₁ → Q₁ < Q₂ → Q₂ < U → False) →
    ∀ f g s u v : R, f ∉ P → g ∉ P → s ∉ P → u ∉ U → u * f - v * g ∈ P →
    (∀ W : Ideal R, W ≤ U → locCycle (P ⊔ Ideal.span {s}) W ≠ 0 →
      locCycle (P ⊔ Ideal.span {f}) W = locCycle (P ⊔ Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (P ⊔ Ideal.span {f}) G - locCycle (P ⊔ Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) U =
      ∑ᶠ W, locCycle (P ⊔ Ideal.span {s}) W *
        locCycle (W ⊔ (P ⊔ Ideal.span {f}).colon {g}) U

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
