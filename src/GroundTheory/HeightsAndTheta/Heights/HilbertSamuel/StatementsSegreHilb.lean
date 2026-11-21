module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegre
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegreHilb.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι)) (n : ℤ),
    hilbFn (segrePrime F q) (fun _ : Unit => n) = hilbFn q (fun _ : K => n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
