import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleListAdditive
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisor_cycle_list_additive : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) ((b + b') :: l) = cycList ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) (b :: l) + cycList ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) (b' :: l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | exact GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycList_divCycle_add_first <;> assumption)
