module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreJoin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section Objects

variable {K : Type} [Fintype K] (ι : K → Type)

abbrev segreIdx : Unit ⊕ K → Type := Sum.elim (fun _ : Unit => ∀ k, ι k) ι

variable (R : Type*) [CommRing R]

def segreIncl : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι →ₐ[R] ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (segreIdx ι) :=
  rename fun v => (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k)

variable {ι R}

def segreY (c : ∀ k, ι k) : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (segreIdx ι) :=
  X (⟨Sum.inl (), c⟩ : Σ k, segreIdx ι k)

def segreMon (c : ∀ k, ι k) : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (segreIdx ι) :=
  ∏ k, X (⟨Sum.inr k, c k⟩ : Σ k, segreIdx ι k)

variable (ι R)

def segreRels : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (segreIdx ι)) :=
  {g | ∃ c d : ∀ k, ι k, g = segreY c * segreMon d - segreY d * segreMon c}

def segreLiftVal (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) : (Σ k, segreIdx ι k) → Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ W)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩))
  | ⟨Sum.inr k, i⟩ => Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩))

def segreLiftMap (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) :
    ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (segreIdx ι) →ₐ[R] Polynomial (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι ⧸ W) :=
  aeval (segreLiftVal ι R W)

def segreLift (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R ι)) : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver R (segreIdx ι)) :=
  RingHom.ker (segreLiftMap ι R W)

end Objects

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
