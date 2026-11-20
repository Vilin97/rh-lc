import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocalizedQuotientIsSimpleModuleOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOrderLe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)), P.IsPrime →
    ∀ (u : J → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι) (G' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (extIdx ι J))) (y : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (extIdx ι J)),
      y ∉ blowUpOf P u → G' ∈ (blowUpOf P u ⊔ Ideal.span {y}).minimalPrimes → IsRelevant G' →
    ∀ x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι, x ∉ P → G'.comap (liftForm (J := J)) ∈ (P ⊔ Ideal.span {x}).minimalPrimes →
    ∀ z : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι, z ∉ P →
      ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P u) (liftForm z)) G' : ℤ) ≤ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P z) (G'.comap (liftForm (J := J))) : ℤ)

def ExceptionalContraction.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog s c → s ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, IsMultiHomog m e → m ∉ P →
    (∀ H, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) H : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ H → m ∉ H) →
    ∀ G' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))),
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))) ∈ G' →
      0 < ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none)) G' : ℤ) →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) G' →
      G'.comap (liftForm (J := BlowUpIdx ι)) ∈ (P ⊔ Ideal.span {s}).minimalPrimes

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
