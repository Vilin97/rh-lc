module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelRefinementGenerating
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

private theorem exists_minor {K : Type} [Field K] {m g : ℕ} (b : Matrix (Fin g) (Fin m) K)
    (b' : Matrix (Fin m) (Fin g) K) (h : b' * b = 1) : ∃ s : Fin m → Fin g, (b.submatrix s id).det ≠ 0 := by
  classical
  have hr : b.rank = m := by
    refine le_antisymm (b.rank_le_width) ?_
    have := Matrix.rank_mul_le_right b' b
    rwa [h, Matrix.rank_one, Fintype.card_fin] at this
  obtain ⟨κ, c, hc, hsp, hli⟩ := exists_linearIndependent' K b.row
  have : Finite κ := Finite.of_injective c hc
  let : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = m := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hr]
  let e : Fin m ≃ κ := (Fintype.equivFinOfCardEq hκ).symm
  have h1 : LinearIndependent K (b.submatrix (c ∘ e) id).row := hli.comp e e.injective
  exact ⟨c ∘ e, ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 h1)).ne_zero⟩

private theorem evalPt_gen {F : Type} [Field F] {Y : Var F} {X : Scheme.{0}} (j : Y.X ⟶ X) (W : X.Opens)
    (hW : ⊤ ≤ (genericPt Y ≫ j) ⁻¹ᵁ W) (h : genericPoint Y.X ∈ j ⁻¹ᵁ W) (a : Γ(X, W)) :
    evalPt (genericPt Y ≫ j) W hW a = fnOf (j ⁻¹ᵁ W) h (j.app W a) := by
  have ht : ⊤ ≤ Y.X.fromSpecStalk (genericPoint Y.X) ⁻¹ᵁ (j ⁻¹ᵁ W) := hW
  have : (Y.X.fromSpecStalk (genericPoint Y.X)).appLE (j ⁻¹ᵁ W) ⊤ ht ≫
      (Scheme.ΓSpecIso (Y.X.presheaf.stalk (genericPoint Y.X))).hom = Y.X.presheaf.germ _ _ h := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app h]
    simp only [Category.assoc]
    have e : (Spec (Y.X.presheaf.stalk (genericPoint Y.X))).presheaf.map
          (homOfLE (le_top : Y.X.fromSpecStalk (genericPoint Y.X) ⁻¹ᵁ (j ⁻¹ᵁ W) ≤ ⊤)).op ≫
        (Spec (Y.X.presheaf.stalk (genericPoint Y.X))).presheaf.map (homOfLE ht).op = 𝟙 _ := by
      rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
    rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
  have e2 := Scheme.Hom.comp_appLE (genericPt Y) j W ⊤ hW
  unfold evalPt
  rw [e2]
  exact congrArg (fun q => q.hom (j.app W a)) this
