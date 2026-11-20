import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalNumberZeroOfHorizontal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_number_zero_of_horizontal : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog f a → f ∉ P → ∀ W, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∉ W → ∀ l : List (K → ℤ), l.length = d → vNumL W l = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.horizontal_vNumL_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Num.horizontal_vNumL_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.horizontal_vNumL_eq_zero <;> assumption)
