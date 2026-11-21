module

public import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem epi_sp {k K : Type} [Field k] [Field K] (a : k →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  have h1 : Flat (spMap a) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat k K)
  have h2 : Surjective (spMap a) := ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

private theorem weil_desc {S : Scheme.{0}} (P : Out.PolAV S) {K Ω : Type} [Field K] [Field Ω] (io : K →+* Ω)
    {y : Sp K ⟶ S} {y' : Sp Ω ⟶ S} (h : Over.mk y' ⟶ Over.mk y) (hl : h.left = spMap io) (q : ℕ)
    (σ σ' : Over.mk y ⟶ P.A) (hσ : σ ^ q = 1) (hσ' : σ' ^ q = 1) (τ τ' : Over.mk y' ⟶ P.A) (e : h ≫ σ = τ)
    (e' : h ≫ σ' = τ') (v : Kˣ) (hv : Out.WeilIs P.A P.L (q : ℤ) τ τ' (unitOn (Units.map (io : K →* Ω) v))) :
    Out.WeilIs P.A P.L (q : ℤ) σ σ' (unitOn v) := by
  subst e e'
  obtain ⟨cq, hcq, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P q σ σ' hσ hσ'
  obtain ⟨u, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq
  have hN := (GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk y)).2 (Over.mk y') h σ σ' (unitOn u) hcq
  rw [hl, GlobalTheory.Ex.Specialise.map_unitOn] at hN
  have hu := GlobalTheory.Ex.Specialise.unitOn_bijective.1
    ((GlobalTheory.LevelCompare.weil_existsUnique P q (h ≫ σ) (h ≫ σ') (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one])
      (by rw [← MonObj.comp_pow, hσ', MonObj.comp_one])).unique hN hv)
  rw [← Units.map_injective io.injective hu]
  exact hcq
