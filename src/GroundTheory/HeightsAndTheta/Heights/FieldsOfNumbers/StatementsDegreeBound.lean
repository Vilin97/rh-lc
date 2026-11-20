import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def EventuallyPolyUnique.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (h : (K → ℤ) → ℤ) (p q : MvPolynomial K ℚ),
    EventuallyPoly h p → EventuallyPoly h q → p = q

def EventuallyPolyShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (h : (K → ℤ) → ℤ) (p : MvPolynomial K ℚ) (c : K → ℤ),
    EventuallyPoly h p → ∃ q : MvPolynomial K ℚ,
      EventuallyPoly (fun m => h (m - c)) q ∧ q.totalDegree ≤ p.totalDegree ∧ (p = 0 → q = 0)

def HilbIrrelevantZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), ¬ IsRelevant I →
    ∀ᶠ m in Filter.atTop, hilbFn I m = 0

def RelevantPrimeDimGe.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)), IsMultiProjPrime P →
    ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι ⧸ P)

theorem EventuallyPolyUnique.hypotheses_example :
    EventuallyPoly (hilbFn (⊥ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (ProjIdx 1)))) (X () + 1) ∧
      EventuallyPoly (hilbFn (⊥ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (ProjIdx 1)))) (X () + 1) :=
  ⟨eventuallyPoly_projectiveLine, eventuallyPoly_projectiveLine⟩

theorem EventuallyPolyShift.hypotheses_example :
    EventuallyPoly (hilbFn (⊥ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (ProjIdx 1)))) (X () + 1) :=
  eventuallyPoly_projectiveLine

theorem HilbIrrelevantZero.hypotheses_example :
    ¬ IsRelevant (Ideal.span (Set.range X) : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (ProjIdx 1))) := by
  intro h
  obtain ⟨i, hi⟩ := h ()
  exact hi (Ideal.subset_span ⟨_, rfl⟩)

theorem RelevantPrimeDimGe.hypotheses_example :
    IsMultiProjPrime (⊥ : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (ProjIdx 1))) :=
  isMultiProjPrime_bot

end

end GroundTheory.Heights₂.Heights.FieldNumbers
