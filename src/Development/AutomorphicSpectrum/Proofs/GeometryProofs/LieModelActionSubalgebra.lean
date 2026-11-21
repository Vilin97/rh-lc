module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModelsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie

theorem lieModel_along_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li) (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li), M₀.IsActOf act.act ρ₀ → ∀ (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L) (toLi : L →ₗ[R] Li), Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧ (∀ v, (M₀.pt (toLi v)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧ ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M₀ B _ act ρ₀ h₀ O _ _ R x hx
  subst hx
  obtain ⟨L, iL, mL, ⟨M⟩⟩ := lieModel_exists X G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X G R x L M B act.act act.hom act.one act.mul act.add
  have hsm : ∀ (a : R) (t : Li), a • t = algebraMap R Ω a • t := fun _ _ => rfl
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ x = spMap (algebraMap R Ω) ≫ x := rfl
  have spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C) :
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (g.comp f)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let φ := algebraMap R Ω
  have hbase : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [spec_comp, spec_comp]
    congr 2
    ext a <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let base : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
    Over.homMk (Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ))) (by
      change _ ≫ _ ≫ x = _ ≫ (spMap φ ≫ x)
      rw [← Category.assoc, hbase, Category.assoc])
  have hfst : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [spec_comp, spec_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [GlobalTheory.CompanionTheory.Ar.dualMap]
  have htan (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
      IsTanAt G (spMap φ ≫ x) (base ≫ v) := by
    change _ ≫ Spec.map _ ≫ v.left = _
    rw [← Category.assoc, hfst, Category.assoc, hv]
    exact congrArg (·.left)
      (comp_one (M := G) (Over.homMk (Spec.map (CommRingCat.ofHom φ)) hφ : Over.mk (spMap φ ≫ x) ⟶ Over.mk x))
  have hscale (c : R) : base ≫ LieTangent.epsScale x c =
      LieTangent.epsScale (spMap φ ≫ x) (φ c) ≫ base := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) =
      Spec.map (CommRingCat.ofHom (epsMul (φ c))) ≫ Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ))
    rw [spec_comp, spec_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    ext <;> simp [GlobalTheory.CompanionTheory.Ar.dualMap, epsMul, mul_comm]
  have ex : ∀ e, ∃ t, M₀.pt t = base ≫ M.pt e :=
    fun e => M₀.onto _ (htan _ (M.tan e))
  choose f hf using ex
  let j : L →ₗ[R] Li :=
    { toFun := f
      map_add' := fun a b => M₀.inj (by rw [M₀.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M₀.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          hscale, Category.assoc]) }
  have hl : ∀ v, (M₀.pt (j v)).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R Ω)) ≫ (M.pt v).left := fun v => by
    change (M₀.pt (f v)).left = _
    rw [hf]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.lie_model_finite_base_change X G R x L M
  refine ⟨L, iL, mL, M, ρ, j, h1, h2, hρ, h3 Ω Li M₀ j hl, hl, fun a v => M₀.inj ?_⟩
  change M₀.pt (f (ρ a v)) = M₀.pt (ρ₀ a (f v))
  rw [h₀ a, hf, hf, hρ a, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie
