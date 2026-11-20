import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocalizedQuotientIsSimpleModuleOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def ResidualDisjoint.Statement : Prop :=
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
      0 < ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s)) G' : ℤ) →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      (newVar none : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))) ∉ G'

def ResidualContraction.Statement : Prop :=
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
      0 < ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s)) G' : ℤ) →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      ∀ x : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, x ∉ P →
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm x)) G' : ℤ) ≤
          ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P x) (G'.comap (liftForm (J := BlowUpIdx ι) (ι := ι) (R := O))) : ℤ)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
