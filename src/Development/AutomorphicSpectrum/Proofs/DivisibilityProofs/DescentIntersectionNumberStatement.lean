module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DescentIntersectionNumber
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_intersection_number : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (F F' : Type) [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F'] (V' : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F' ι)), IsMultiHomogIdeal V' → (∀ (c : ∀ k, ι k) (a : F'), ∃ (n : ℕ) (G : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), IsMultiHomog G (fun _ => n) ∧ C a * (∏ k, X ⟨k, c k⟩) ^ n - MvPolynomial.map (algebraMap F F') G ∈ V') → ∀ l : List (K → ℤ), intNumL F (V'.comap (MvPolynomial.map (algebraMap F F'))) l = (Module.finrank F F' : ℤ) * intNumL F' V' l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.intNumL_subfield_constants | exact GlobalTheory.CompanionTheory.Ar.Num.intNumL_subfield_constants | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.intNumL_subfield_constants <;> assumption)
