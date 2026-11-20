import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def HilbNegDimZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiHomogIdeal I → IsRelevant I →
    relDim I < 0 → ∀ᶠ m in Filter.atTop, hilbFn I m = 0

abbrev pointCoord : Σ _ : Unit, ProjIdx 0 () := ⟨(), 0⟩

def pointSquareIdeal (F : Type*) [Field F] : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (ProjIdx 0)) :=
  Ideal.span ((fun s => monomial s (1 : F)) '' {Finsupp.single pointCoord 2})

end

end GroundTheory.Heights₂.Heights.FieldNumbers
