module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrameStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem exists_local {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} {Y : Var F}
    {ρ : Y.X ⟶ gen Z} (hρ : ρ ≫ genStr Z ≫ spMap e.toRingHom = Y.str) (g₀ : GenFrame e ρ) (τ : E →+* ℂ) (y : Y.X) :
    ∃ (U : (gen Z).Opens) (P : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Y.Fn), ρ y ∈ U ∧
      ∀ z : Y.X, ρ z ∈ U → ∃ φ f, Fits g₀ τ z φ f P := by
  obtain ⟨U, hU, φ, f, hy, hφ, -⟩ := GlobalTheory.T.exists_affine_stable_lie_eigenspace_frame E H Dw l Xo c O β Z (ρ y)
  have hg : ⊤ ≤ (genericPt Y ≫ ρ) ⁻¹ᵁ U := gen_le ρ hy
  let χ : Γ(gen Z, U) →+* Y.Fn := evalPt (genericPt Y ≫ ρ) U hg
  have hχ : genericPt Y ≫ ρ = spMap χ ≫ hU.fromSpec := eq_spec_fromSpec hU _ hg
  have hc : constF e Y = χ.comp φ := EigLoc.spMap_inj (by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (GlobalTheory.FlagBundle.ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    have h3 : spMap (χ.comp φ) = spMap χ ≫ spMap φ := by rw [← Spec.map_comp]; rfl
    have h4 : spMap (constF e Y) = spMap (algebraMap F Y.Fn) ≫ spMap e.symm.toRingHom := by rw [← Spec.map_comp]; rfl
    have h5 : spMap χ ≫ spMap φ = (genericPt Y ≫ ρ) ≫ genStr Z := by
      rw [hχ, ← hφ]; exact (Category.assoc _ _ _).symm
    rw [h3, h4, h5, ← h1, ← hρ]
    simp only [Category.assoc, h2, Category.comp_id])
  obtain ⟨f', hf'⟩ := f.exists_isMap χ (x' := genericPt Y ≫ ρ ≫ genι Z) hc
    (by rw [← Category.assoc, hχ]; exact Category.assoc _ _ _)
  refine ⟨U, g₀.co f' τ, hy, fun z hz => ?_⟩
  have hs : ⊤ ≤ (stalkPt Y z ≫ ρ) ⁻¹ᵁ U := stalk_le ρ hz
  let ψ : Γ(gen Z, U) →+* Y.X.presheaf.stalk z := evalPt (stalkPt Y z ≫ ρ) U hs
  have hψ : stalkPt Y z ≫ ρ = spMap ψ ≫ hU.fromSpec := eq_spec_fromSpec hU _ hs
  have hcomp : (toFn z).comp ψ = χ := EigLoc.spMap_inj ((cancel_mono hU.fromSpec).1 (by
    have h3 : spMap ((toFn z).comp ψ) = spMap (toFn z) ≫ spMap ψ := by rw [← Spec.map_comp]; rfl
    refine Eq.trans ?_ hχ
    rw [h3, ← spMap_toFn z, Category.assoc, Category.assoc, hψ]))
  obtain ⟨k, hk⟩ := f.exists_isMap ψ (x' := stalkPt Y z ≫ ρ ≫ genι Z) rfl
    (by rw [← Category.assoc, hψ]; exact Category.assoc _ _ _)
  have hc' : constF e Y = (toFn z).comp (ψ.comp φ) := by rw [← RingHom.comp_assoc, hcomp, hc]
  have hm : k.IsMap (toFn z) f' := fun τ i => by
    rw [hf', hk, GlobalTheory.GradedPieces.dual_comp, hcomp]
  refine ⟨_, k, hc', fun i => ?_⟩
  rw [← hm τ i]
  exact g₀.co_spec f' τ i
