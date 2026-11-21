module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def SmallSectionMixed.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M H : HermLine ι) (p q : ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (H.a = fun _ => (1 : ℤ)) → IsSemipositiveRel P0 P H → MonomialsBounded P H (fun _ => 1) → IsConjInvariantH H →
    1 ≤ p → 0 < II K ι P d (fun _ => ((_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow M q).tensor (_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow H p))) →
    ∃ (n : ℕ) (f g : MRing ι), 1 ≤ n ∧ IsRatSectionOn P ((_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow M ((n * q : ℕ) : ℤ)).tensor (_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow H ((n * p : ℕ) : ℤ))) f g ∧
      divCycle P g ≤ divCycle P f ∧
      ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤
        ‖eval z (map (Int.castRingHom ℂ) g)‖ * ((_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow M ((n * q : ℕ) : ℤ)).tensor (_root_.GroundTheory.Heights₂.Heights.Inter.hermZpow H ((n * p : ℕ) : ℤ))).h z

end GroundTheory.Heights₂.Heights.HilbertSamuel
