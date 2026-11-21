module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsIntegralSegreChartProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver PBlk IsMultiHomogIdeal)
open ComplexSets

def SegreChartZeroSet.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal P → zeroSet (segreChartIdeal P σ i) = segreChartSet P σ i

end GroundTheory.Heights₂.Heights
