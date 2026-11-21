import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem ext_uniq {X : Scheme.{0}} {O : Type} [CommRing O] (s : X ⟶ Sp O) [IsProper s] {C : Type}
    [NontriviallyNormedField C] [IsUltrametricDist C] (x y : Sp ↥(Formalism.MainNotions.DIV.Cons.intO C) ⟶ X)
    (h : spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ y = spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype ≫ x) : y = x := by
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from s]; infer_instance⟩
  have : IsDominant (spMap (Formalism.MainNotions.DIV.Cons.intO C).subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (Formalism.MainNotions.DIV.Cons.intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h
