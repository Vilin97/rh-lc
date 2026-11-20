import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelTrivLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ShiftVolumeBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q →
      arVolP (IsSmallH (mCoordIdeal y) y ((_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow A (q : ℤ)).tensor (_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow (fsH ι) 1)))
          (chartLat y ((_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow A (q : ℤ)).tensor (_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow (fsH ι) 1)).a) 1 D ≤
        C * ((q : ℝ) + 1) * (genDeg (mCoordIdeal y) D ((_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow A (q : ℤ)).tensor (_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow (fsH ι) 1)).a : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
