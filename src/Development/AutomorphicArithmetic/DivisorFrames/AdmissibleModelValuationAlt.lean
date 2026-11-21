module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointOfIntegralPoint
public import Development.AutomorphicArithmetic.DivisorFrames.DominatingModelsSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrier
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing

@[expose] public section

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
