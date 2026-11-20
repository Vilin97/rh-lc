import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FibreComponentDivisorProperties
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_component_divisor_properties : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d → (∀ W, IsFibreComp P W ↔ ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C ϖ)) W : ℤ) ≠ 0) ∧ (∀ (a : K → ℕ) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog f a → f ∉ P → ∀ W, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) ≠ 0 → (C ϖ : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) ∈ W → IsFibreComp P W) ∧ ∀ (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsVerticalDivisor P ϖ b f g → ∀ W, ratDiv P f g W ≠ 0 → IsFibreComp P W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FibreComp.fibre_comp | exact GlobalTheory.CompanionTheory.Ar.Num.FibreComp.fibre_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FibreComp.fibre_comp <;> assumption)
