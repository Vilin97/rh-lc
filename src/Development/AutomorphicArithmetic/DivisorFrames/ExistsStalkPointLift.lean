module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem exists_rho {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (w : Sp R ⟶ X) (x : X)
    (hx : w (closedPoint R) = x) : ∃ ρ : X.presheaf.stalk x →+* R, spMap ρ ≫ X.fromSpecStalk x = w := by
  subst hx
  exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) w⟩

private theorem hom_ext' {R : Type} [CommRing R] {X : Scheme.{0}} {x : X} {f g : X.presheaf.stalk x →+* R}
    (h : spMap f ≫ X.fromSpecStalk x = spMap g ≫ X.fromSpecStalk x) : f = g := by
  have h1 : spMap f = spMap g := (cancel_mono (X.fromSpecStalk x)).1 h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

private theorem gen_eq {X : Scheme.{0}} [IsIntegral X] (x : X) :
    spMap (algebraMap (X.presheaf.stalk x) X.functionField) ≫ X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
