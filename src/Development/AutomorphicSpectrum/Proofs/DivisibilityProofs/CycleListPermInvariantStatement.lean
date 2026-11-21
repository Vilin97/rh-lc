module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariant
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cycle_list_perm_invariant : (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (l l' : List (K → ℤ)), l.Perm l' → intNumL F V l = intNumL F V l') ∧ (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Z : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) → ℤ) (l l' : List (K → ℤ)), l.Perm l' → cycList Z l = cycList Z l') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.numbers_list_perm | exact GlobalTheory.CompanionTheory.Ar.Num.numbers_list_perm | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.numbers_list_perm <;> assumption)
