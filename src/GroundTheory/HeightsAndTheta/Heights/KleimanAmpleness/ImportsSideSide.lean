module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftVal
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericDVRSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver intNum IsMultiProjPrime)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def SegreFibreIdeal.Statement : Prop :=
  ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (F : Type) [Field F] (φ : O →+* F)
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω),
    segreRels ι F ⊆ ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) : Set _) ∧
    (mIdealOver O y).map (MvPolynomial.map φ) ≤
      ((mIdealOver O (segreJoin y)).map (MvPolynomial.map φ)).comap (segreIncl ι F) ∧
    ∀ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver F ι), (mIdealOver O y).map (MvPolynomial.map φ) ≤ W →
      (mIdealOver O (segreJoin y)).map (MvPolynomial.map φ) ≤ segreLift ι F W

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
