import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem valAt_alg {K : Type} [Field K] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z] (y : Sp K ⟶ Z)
    (a : Z.presheaf.stalk (below y)) :
    TrueGeo.valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [TrueGeo.valAt, dif_pos h, IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec]

private theorem valAt_mul' {K : Type} [Field K] {Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral Z] {y : Sp K ⟶ Z}
    {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    TrueGeo.valAt y (f * g) = TrueGeo.valAt y f * TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_alg, valAt_alg, valAt_alg, map_mul]
