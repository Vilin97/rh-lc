module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalDivisorGeometricNumber
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_divisor_geometric_number : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι)) (D : ℕ), IsArithVar P (D + 1) → ∀ (a : K → ℕ) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι), IsMultiHomog f a → f ∉ P → ∀ W, ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ) ≠ 0 → ∀ (p : ℕ) [Fact p.Prime], (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℤ ι) ∈ W → charOf W = p ∧ ¬ IsHorizontal W ∧ ∀ L : Fin D → K → ℤ, geoNum D W L = intNum (ZMod p) (extTo (ZMod p) W) L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum | exact GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp.geoNum_eq_intNum <;> assumption)
