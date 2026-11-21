module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm
