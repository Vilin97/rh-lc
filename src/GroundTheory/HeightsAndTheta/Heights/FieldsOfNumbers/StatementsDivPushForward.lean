import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivPushForward.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι')) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))), IsMultiHomog a c →
    a ∉ contractPrime j P' →
    ∀ (N' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι') → ℤ) (N : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F (fun k => ι' (j k))) → ℤ),
      (∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) →
        relDim (contractPrime j W') = (n : ℕ) →
        haveI := hW'.isPrime
        N' W' = relDeg j W' * N (contractPrime j W')) →
      (∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) → relDim (contractPrime j W') < (n : ℕ) →
        N' W' = 0) →
      haveI := hP'.isPrime
      cycEval N' ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P' (rename (blockIncl j ι') a)) W : ℤ))) =
        relDeg j P' * cycEval N ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle (contractPrime j P') a) W : ℤ)))

open Classical in

theorem DivPushForward.hypotheses_example :
    let P' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (addBlock (ProjIdx 1) 0)) := ⊥
    let N : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k))) → ℤ := fun _ => 1
    let N' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (addBlock (ProjIdx 1) 0)) → ℤ := fun W' =>
      if h : W'.IsPrime ∧ relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') = ((0 : ℕ) : WithBot (WithTop ℤ)) then
        haveI := h.1; (relDeg (Function.Embedding.some : Unit ↪ Option Unit) W' : ℤ) * N (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') else 0
    IsMultiProjPrime P' ∧ relDim P' = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) ∧
      relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) P') = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) ∧
      IsMultiHomog (X ⟨(), (0 : Fin 2)⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k)))
        (blockWeight (ProjIdx 1) ⟨(), 0⟩) ∧
      (X ⟨(), (0 : Fin 2)⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℚ (fun k => addBlock (ProjIdx 1) 0 ((Function.Embedding.some : Unit ↪ Option Unit) k))) ∉ contractPrime (Function.Embedding.some : Unit ↪ Option Unit) P' ∧
      (∀ W' (hW' : IsMultiProjPrime W'), relDim W' = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        haveI := hW'.isPrime
        N' W' = relDeg (Function.Embedding.some : Unit ↪ Option Unit) W' * N (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W')) ∧
      (∀ W', IsMultiProjPrime W' → relDim W' = ((0 : ℕ) : WithBot (WithTop ℤ)) →
        relDim (contractPrime (Function.Embedding.some : Unit ↪ Option Unit) W') < ((0 : ℕ) : WithBot (WithTop ℤ)) → N' W' = 0) := by
  intro P' N N'
  obtain ⟨h1, h2, h3⟩ := ProjectionFormulaDegree.hypotheses_example
  refine ⟨h1, h2, h3, coordinate_isMultiHomog 1 0, ?_, ?_, ?_⟩
  · rw [show P' = ⊥ from rfl, contractPrime_bot, Ideal.mem_bot]
    exact X_ne_zero _
  · intro W' hW' _ hc
    show (if h : _ then _ else _) = _
    rw [dite_eq_left ⟨hW'.isPrime, hc⟩]
  · intro W' _ _ hc
    show (if h : _ then _ else _) = _
    rw [dite_eq_right (fun h => (ne_of_lt hc) h.2)]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
