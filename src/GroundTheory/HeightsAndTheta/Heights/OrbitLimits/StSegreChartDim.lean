module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartObjects
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver PBlk IsArithVar)

def SegreChartDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsArithVar P (e + 1) → ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)

end GroundTheory.Heights₂.Heights
