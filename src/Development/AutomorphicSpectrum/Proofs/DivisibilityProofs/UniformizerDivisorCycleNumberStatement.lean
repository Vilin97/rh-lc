module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UniformizerDivisorCycleNumber
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_divisor_cycle_number : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d → ∀ (u : Oˣ) (e : ℕ) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C ((u : O) * ϖ ^ e))) W : ℤ))) cls H Q = (e : ℝ) * genNum (FractionRing O) (genFib P) cls H Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const <;> assumption)
