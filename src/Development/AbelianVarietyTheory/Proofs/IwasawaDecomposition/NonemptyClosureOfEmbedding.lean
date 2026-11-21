module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DRFlag GlobalTheory.ProjSpace
open GlobalTheory.FlagMod (ev ev_spMap le_preimage_comp)

namespace GlobalTheory.SubClosure

section General

variable {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] {N : ℕ}

instance subsingleton_sp (K : Type) [Field K] : Subsingleton (Sp K) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

end General

section Main

variable {O : Type} [CommRing O] {Z : Scheme.{0}} (s : Z ⟶ Sp O) {C : Coc Z} {N : ℕ} (Em : C.Emb N)
  {ch : Charts Z} {r : ℕ} (D : C.Sub ch r)

end Main

end GlobalTheory.SubClosure
