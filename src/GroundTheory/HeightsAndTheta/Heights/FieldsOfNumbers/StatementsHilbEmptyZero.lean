import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

universe u

def HilbEmptyZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), (∀ W ∈ I.minimalPrimes, ¬ IsRelevant W) →
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0

noncomputable def HilbEmptyZero.blockIdeal (k : Fin 2) : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (fun _ : Fin 2 => Fin 2)) :=
  Ideal.span (Set.range fun i : Fin 2 => (X ⟨k, i⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (fun _ : Fin 2 => Fin 2)))

end GroundTheory.Heights₂.Heights.FieldNumbers
