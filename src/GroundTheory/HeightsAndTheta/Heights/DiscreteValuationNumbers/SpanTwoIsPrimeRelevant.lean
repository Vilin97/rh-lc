module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsMultiHomogIdealSpanSingleton
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMultAtPrimeAtMinimal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Defs

variable {K : Type*} {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def commonExcess (ϖ : O) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (f g s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) : ℕ :=
  ⨆ G : {G : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) // (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G}, (((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G.1 : ℤ) * ratDiv P f g G.1).toNat

end Defs

section Lemmas

def NoCommonComponentCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∀ G, (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G → ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) ≠ 0 → ratDiv P f g G = 0) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

def CommonFactorInduction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    (∃ G, (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ G ∧ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) G : ℤ) ≠ 0 ∧ ratDiv P f g G ≠ 0) →
    (∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι')) (d' : ℕ), IsModelOver P' (d' + 1) →
      ∀ (b' : K' → ℤ) (f' g' : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι'), IsEffectiveVertical P' ϖ b' f' g' →
      ∀ (c' : K' → ℕ) (s' : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι'), IsMultiHomog s' c' → s' ∉ P' →
      (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P' s') H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι') ∉ H → IsVerticalDivisor H ϖ b' f' g') →
      commonExcess ϖ P' f' g' s' < commonExcess ϖ P f g s →
      ∀ L' : Fin d' → K' → ℤ, cutIdentity ϖ P' b' f' g' c' s' L') →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
