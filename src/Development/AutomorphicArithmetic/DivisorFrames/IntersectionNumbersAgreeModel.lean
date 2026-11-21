module

public import Mathlib
public import Development.AutomorphicArithmetic.DivisorFrames.IntersectionNumberPullbackDegree
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsNormalCommonModel
public import Development.AutomorphicArithmetic.DivisorFrames.PullCartierPicAgree
public import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl
