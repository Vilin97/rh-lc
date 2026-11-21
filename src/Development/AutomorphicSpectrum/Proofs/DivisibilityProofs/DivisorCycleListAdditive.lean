module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import Development.WeilBound.CoreStatements.IdealCycleValues.CycListAdditiveFirstClass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycList_divCycle_add_first : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι)) (d : ℕ), IsModelOver P d → ∀ (a : K → ℕ) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι), IsMultiHomog f a → f ∉ P → ∀ (b b' : K → ℤ) (l : List (K → ℤ)), l.length + 1 = d → cycList ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) ((b + b') :: l) = cycList ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) (b :: l) + cycList ((fun W => ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f) W : ℤ))) (b' :: l) := by
  exact @BaseChangeColon.cycList_additive_first_class

end GlobalTheory.CompanionTheory.Ar.Num
