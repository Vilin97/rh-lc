import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def BlowUpStrictTransform.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsVerticalDivisor P ϖ b f g →
    ∀ s : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι, s ∉ P → ∀ (e : K → ℕ) (m : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    ∀ H : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))),
      (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (extIdx ι (BlowUpIdx ι))) ∉ H →
      (((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s)) H : ℤ) ≠ 0 ∨
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none)) H : ℤ) ≠ 0) →
      ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) (H.comap (liftForm (J := BlowUpIdx ι))) : ℤ) ≠ 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
