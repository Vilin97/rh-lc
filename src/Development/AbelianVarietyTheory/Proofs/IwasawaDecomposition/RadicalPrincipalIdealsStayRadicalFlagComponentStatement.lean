module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFullFlagFamilyLieCompatibleGradedStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseMapOfFunctionFieldsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyFieldStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGeneric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagFramesFlagComponentPullbackBaseFramesStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameStableOfIsLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleComp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionFieldMapFullFlagGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.exists_functionField_map_fullFlag_generic_point : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∃ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ ∧ CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) := by
  first | exact @GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | exact GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic | (intros; apply GlobalTheory.FlagBundle.exists_fieldMap_coBear_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ y : Y₁.X, ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  first | exact @GlobalTheory.FlagBundle.dominates_O | exact GlobalTheory.FlagBundle.dominates_O | (intros; apply GlobalTheory.FlagBundle.dominates_O <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBearsFlagsOfGenericStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlagBundleMorphism_bearsFlags_of_generic : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ g : Y₁.X ⟶ Y₂.X, (ratOf Y₂).IsHom (ratOf Y₁) ψ g → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g) := by
  first | exact @GlobalTheory.FlagBundle.coBear_comp_of_isHom | exact GlobalTheory.FlagBundle.coBear_comp_of_isHom | (intros; apply GlobalTheory.FlagBundle.coBear_comp_of_isHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical


theorem _root_.GlobalTheory.T.fullFlagBundleMorphism_bijective_fieldPoints : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  first | exact @GlobalTheory.FlagBundle.CoBear₂ | exact GlobalTheory.FlagBundle.CoBear₂ | (intros; apply GlobalTheory.FlagBundle.CoBear₂ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalRStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical


theorem _root_.GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') → ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | exact GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | (intros; apply GlobalTheory.ZH.RatModel.exists_isHom_of_map_O <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentClassifyingMapBijectiveOnGeometricPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.ClsMap

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (Y' : Var F) (φ' : X.Fn →ₐ[F] Y'.Fn) (f' : Y'.X ⟶ X.X) (S' : Fr (ratOf Y') Dw.mult Dw.mult), Refines Eb S' φ' f' → ∃ h : C.Y.X ⟶ Y'.X, h ≫ f' = f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ C.Y.X => p ≫ h) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hjo hj f hπ f₀ Eb A₀ hT hL Y' φ' f' S' hR'

  obtain ⟨φ, hφ⟩ := GlobalTheory.T.flagSpaceComponent_baseMap_of_functionFields E H Dw l Xo c O β Z F e C X j hjo hj f hπ hL
  have hgen : genericPt C.Y ≫ f = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X := hφ
  have hx : genericPt C.Y ≫ C.π ≫ genι Z = spMap (φ : X.Fn →+* C.Y.Fn) ≫ genericPt X ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, ← Category.assoc, hgen, Category.assoc]
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hst₀ : f₀.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ f₀ inferInstance
  obtain ⟨⟨M, hM, -⟩, hMu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ f₀ C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (φ : X.Fn →+* C.Y.Fn) inferInstance hst₀ hx hc).1 C.f0
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₀φ : ∀ τ, ((A₀.map φ) τ).det ≠ 0 := fun τ =>
    (Mat.det_map A₀ (φ : X.Fn →+* C.Y.Fn) τ).trans_ne ((map_ne_zero _).2 (hA₀d τ))
  set A₁ : Mat Dw.mult C.Y.Fn := M * A₀.map φ with hA₁
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := fun τ => by
    rw [hA₁, Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hMu M hM τ).ne_zero (hA₀φ τ)
  have hC : f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) := by
    rw [hA₁, mul_assoc, Mat.mul_inv hA₀φ, mul_one]; exact hM
  obtain ⟨E', hT', -⟩ := GlobalTheory.T.exists_fullFlagFamily_lieCompatible_graded E H Dw l Xo c O β Z F e C A₁ hA₁d
  have hsub := GlobalTheory.T.fullFlagFrames_flagComponent_pullback_baseFrames E H Dw l Xo c O β Z F e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hC
  have R₁ : Reps Eb E' φ f := ⟨hφ, hsub,
    GlobalTheory.T.flagSpace_unique_lift_any_field E H Dw l Xo c O β Z F e C X j hjo hj f hπ f₀ Eb A₀ hT hL φ hφ E' A₁ hT' hC hsub⟩
  have R₂ : Reps Eb S' φ' f' := hR'.reps

  obtain ⟨ψ, hψ, hG⟩ := GlobalTheory.T.exists_functionField_map_fullFlag_generic_point F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂
  obtain ⟨h, hh⟩ := GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing F Y'.Fn (ratOf Y') C.Y.Fn (ratOf C.Y) ψ
    (GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ ψ hψ hG)
  have hf : h ≫ f' = f := by
    have h1 := R₂.1.comp hh
    rw [hψ] at h1
    exact h1.unique hφ
  refine ⟨h, hf, fun K _ _ => GlobalTheory.T.fullFlagBundleMorphism_bijective_fieldPoints F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ h hf
    (GlobalTheory.T.fullFlagBundleMorphism_bearsFlags_of_generic F (E →+* ℂ) Dw.mult X C.Y Y' Eb E' φ f S' φ' f' R₁ R₂ ψ hψ hG h hh) K⟩

end GlobalTheory.ShFam.ClsMap
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentClassifyingMapBijectiveGeomPoiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.flagSpaceComponent_classifyingMap_bijective_geomPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (Y' : Var F) (φ' : X.Fn →ₐ[F] Y'.Fn) (f' : Y'.X ⟶ X.X) (S' : Fr (ratOf Y') Dw.mult Dw.mult), Refines Eb S' φ' f' → ∃ h : C.Y.X ⟶ Y'.X, h ≫ f' = f ∧ ∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ C.Y.X => p ≫ h) := by
  first | exact @GlobalTheory.ShFam.ClsMap.main | exact GlobalTheory.ShFam.ClsMap.main | (intros; apply GlobalTheory.ShFam.ClsMap.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar


theorem _root_.GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F) (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str → (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) → IsIso h := by
  first | exact @GlobalTheory.BijPointsIso.isIso_of_bijective_points | exact GlobalTheory.BijPointsIso.isIso_of_bijective_points | (intros; apply GlobalTheory.BijPointsIso.isIso_of_bijective_points <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RadicalPrincipalIdealsStayRadicalFlagComponent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.FlagCptRad

theorem isHom_apply_eq {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    {M : GlobalTheory.ZH.RatModel F Ω} {M' : GlobalTheory.ZH.RatModel F Ω'} {φ ψ : Ω →ₐ[F] Ω'} {f : M'.Z ⟶ M.Z}
    (hφ : M.IsHom M' φ f) (hψ : M.IsHom M' ψ f) (x : Ω) : φ x = ψ x := by
  have hx : ∀ w, x ∈ M.O (f (M'.pt w)) := fun w => by
    have e1 : (M'.pt ≫ f) w = f (M'.pt w) := Scheme.Hom.comp_apply _ _ _
    have e2 : (M'.pt ≫ f) w = genericPoint M.Z := by
      rw [hφ, Scheme.Hom.comp_apply, M.pt_apply]
    rw [← e1, e2, M.O_genericPoint]; exact Algebra.mem_top
  have h1 := hφ.val_comp M'.pt (IsLocalRing.closedPoint Ω') (hx _)
  have h2 := hψ.val_comp M'.pt (IsLocalRing.closedPoint Ω') (hx _)
  rw [GlobalTheory.ZH.RatModel.val_pt] at h1 h2
  exact h1.symm.trans h2

theorem keepsRad_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → KeepsRad (ratOf X) (ratOf C.Y) φ f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j hj hjs f hf f₀ Eb A₀ hT hlift φ hφ
  haveI : CharZero F := RingHom.charZero e.toRingHom
  obtain ⟨Y', φ', f', S', -, hR⟩ := tower _ (ratOf X) X.dim Eb (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  change Y'.X ⟶ X.X at f'
  obtain ⟨h, hh, hbij⟩ := GlobalTheory.T.flagSpaceComponent_classifyingMap_bijective_geomPoints E H Dw l Xo c O β Z F e C X j hj hjs f hf f₀ Eb A₀ hT hlift Y' φ' f' S' hR
  have hs' : f' ≫ X.str = Y'.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hstr : h ≫ Y'.str = C.Y.str := by
    rw [← hs', ← Category.assoc, hh, ← hjs, ← C.π_str, ← hf, Category.assoc]
  have hiso : IsIso h := GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero F C.Y Y' h hstr hbij
  obtain ⟨ψ, S'', hR2⟩ := exists_refines_of_iso (ratOf Y') (ratOf C.Y) (@asIso _ _ _ _ h hiso) hstr S'
  have hR2' : Refines S' S'' ψ h := hR2
  subst hh
  have hR3 := hR.comp hR2'
  have hrad : KeepsRad (ratOf X) (ratOf C.Y) (ψ.comp φ') (h ≫ f') := hR3.rad
  have hhom : (ratOf X).IsHom (ratOf C.Y) (ψ.comp φ') (h ≫ f') := hR3.hom
  intro z' g hg
  rw [isHom_apply_eq hφ hhom g]
  exact hrad z' g hg

end GlobalTheory.FlagCptRad
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RadicalPrincipalIdealsStayRadicalFlagComponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical


theorem _root_.GlobalTheory.T.radical_principal_ideals_stay_radical_flag_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → KeepsRad (ratOf X) (ratOf C.Y) φ f := by
  first | exact @GlobalTheory.FlagCptRad.keepsRad_of_flagCpt | exact GlobalTheory.FlagCptRad.keepsRad_of_flagCpt | (intros; apply GlobalTheory.FlagCptRad.keepsRad_of_flagCpt <;> assumption)
end
end
