module

public import Mathlib
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem genericPoints_subset_range_j :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O]
      (β : O →+* c.F) (Y : Model Xo c β),
      IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) →
        genericPoints Y.X ⊆ Set.range Y.j :=
  @PositivityTheory.HtPt.Ml.generic_points_range

end GlobalTheory.CompanionTheory.Ar.M0
