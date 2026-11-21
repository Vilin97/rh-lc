import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
import Development.AutomorphicArithmetic.DivisorFrames.DominatingModelsSpherical
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem bc_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X} {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (ρ : A →+* B) (χ : B →+* C) (u : Vecs Dw t A) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    u.bc (χ.comp ρ) σ j = spMap (dualMap χ) ≫ u.bc ρ σ j := by
  rw [Vecs.bc, Vecs.bc, ← Category.assoc, ModelRelProbe.spMap_comp]
  congr 2
  ext z <;> simp [dualMap]
