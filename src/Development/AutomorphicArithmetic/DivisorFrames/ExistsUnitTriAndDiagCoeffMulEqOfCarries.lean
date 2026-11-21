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

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

private theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero (Y : GlobalTheory.ProjVar.Var F) (y : Y.X) :
    spMap (algebraMap (Y.X.presheaf.stalk y) Y.X.functionField) ≫ stalkPt Y y = genericPt Y :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

end SlopeTestRemainingChoices
