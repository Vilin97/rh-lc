module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianHodge

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)

private theorem local_mem_F1_iff_supported (hO : Function.Injective (cmpO s)) (c : FirstDeRham s) :
    c ∈ F1 s ↔ cmp1 s c ∈ CechHodgeFiltration s := by
  change toH1O s c = 0 ↔ toHO1 s (cmp1 s c) = 0
  rw [structureSheaf_comparison_comm]
  exact ⟨fun h ↦ h ▸ map_zero _, fun h ↦ hO (h.trans (map_zero _).symm)⟩

private theorem local_hodge_of_cmp (P : Submodule R (FirstDeRham s)) (hP : P = ⊤)
    (hb : Function.Bijective (cmp1 s)) (hO : Function.Injective (cmpO s)) (t : X ⟶ Sp R) (hst : s = t)
    (hcl : ClosedForm t = ⊤) (hinj : Function.Injective (clForm t))
    (hsurj : Function.Surjective (toHO1 t)) (hproj : Module.Projective R (HO1 t)) :
    (∃ N : Submodule R P, IsCompl ((F1 s).comap P.subtype) N) ∧
      Nonempty (((F1 s).comap P.subtype) ≃ₗ[R] GlobForm t) := by
  subst hst
  let E : P ≃ₗ[R] HH1 s := (LinearEquiv.ofTop P hP).trans (LinearEquiv.ofBijective (cmp1 s) hb)
  have hE : ∀ x : P, E x = cmp1 s x.1 := fun _ ↦ rfl
  have hc : (F1 s).comap P.subtype = (CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s) := by
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe, hE]
    exact local_mem_F1_iff_supported s hO x.1
  obtain ⟨N', hN'⟩ := exists_isCompl_ker (toHO1 s) hsurj
  refine ⟨⟨N'.comap (E : P →ₗ[R] HH1 s), ?_⟩, ⟨?_⟩⟩
  · rw [hc, Submodule.comap_equiv_eq_map_symm, Submodule.comap_equiv_eq_map_symm]
    exact (Submodule.orderIsoMapComap E.symm).isCompl hN'
  · let e1 : ((F1 s).comap P.subtype) ≃ₗ[R] ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) :=
      LinearEquiv.ofEq _ _ hc
    let e2 : ((CechHodgeFiltration s).comap (E : P →ₗ[R] HH1 s)) ≃ₗ[R] CechHodgeFiltration s :=
      E.ofSubmodules _ (CechHodgeFiltration s) (Submodule.map_comap_eq_of_surjective E.surjective _)
    let e3 : CechHodgeFiltration s ≃ₗ[R] LinearMap.range (clForm s) := LinearEquiv.ofEq _ _ (cechHodgeFiltration_eq_range s)
    let e4 : LinearMap.range (clForm s) ≃ₗ[R] ClosedForm s := (LinearEquiv.ofInjective (clForm s) hinj).symm
    let e5 : ClosedForm s ≃ₗ[R] GlobForm s := LinearEquiv.ofTop _ hcl
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))


private theorem local_abelianDeRham_hodge (P1 : GlobalTheory.Published.CrystallineSmoothLift) (P2 : GlobalTheory.Published.AbelianHodgeDeRham) :
    GlobalTheory.Published.AbelianDeRham.Hodge := by
  intro R _ A _ g hA hg
  obtain ⟨h0, -⟩ := GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison P1 P2) R A g hA hg
  obtain ⟨-, -, ⟨hGf, hGp, hGr⟩, ⟨-, hOp, -⟩, ⟨hcl, hinj, hsurj⟩, -⟩ := P2 R A g hA hg
  have := hA.smooth
  have := hA.proper
  obtain ⟨hb, -⟩ := cechDeRham_comparison_bijective_cup_smooth P1 R A.left (A.hom ≫ 𝟙 _) inferInstance inferInstance
    inferInstance
  have hO := GlobalTheory.T.structure_sheaf_comparison_injective R A.left (A.hom ≫ 𝟙 _)
  obtain ⟨⟨N, hN⟩, ⟨e⟩⟩ := local_hodge_of_cmp (A.hom ≫ 𝟙 _) (primDR A) h0 hb hO A.hom
    (Category.comp_id _) hcl hinj hsurj hOp
  exact ⟨GlobalTheory.T.hodgeLieSequence_exact_abelianScheme P1 P2 R A g hA hg, ⟨N, hN⟩, Module.Finite.equiv e.symm,
    Module.Projective.of_equiv e.symm, fun p ↦ by
      change Module.rankAtStalk ((F1 (A.hom ≫ 𝟙 _)).comap (primDR A).subtype) p = g
      rw [Module.rankAtStalk_eq_of_equiv e, hGr]⟩


end GlobalTheory.AbelianHodge

namespace GlobalTheory

theorem abelianDeRham_free_hodge_baseChange : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.Hodge ∧
      GlobalTheory.Published.AbelianDeRham.BaseChange := by
  intro hH
  obtain ⟨hF, hBC, -⟩ := GlobalTheory.abelianDeRham_free_baseChange_rigid hH
  exact ⟨hF, GlobalTheory.AbelianHodge.local_abelianDeRham_hodge
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH, hBC⟩

end GlobalTheory
