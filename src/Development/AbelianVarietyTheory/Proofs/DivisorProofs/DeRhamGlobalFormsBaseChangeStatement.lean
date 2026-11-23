module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1SurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivGlobalOneFormsBaseChangeStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfFormInjectiveOfH0Const
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClosedFormClassStatement
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMap

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem exists_grpObj_isAbelianScheme_of_isPullback_spMap : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  intro R _ A _ g hA hg R' _ σ X' s' φ h
  have hsm : SmoothOfRelativeDimension g s' := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := g)
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h hg
  let B := (Over.pullback (spMap σ)).obj A
  letI : GrpObj B := Functor.grpObjObj
  let e : B ≅ Over.mk s' := Over.isoMk h.isoPullback.symm (by simp [B])
  letI : GrpObj (Over.mk s') := GrpObj.ofIso e
  refine ⟨this, ?_, hsm⟩
  have hc := hA.comm
  have hcB : IsCommMonObj B := Functor.isCommMonObj_obj
  exact {
    comm := by
      constructor
      show (β_ _ _).hom ≫ ((e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom) = (e.inv ⊗ₘ e.inv) ≫ μ[B] ≫ e.hom
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
        ← Category.assoc (β_ B B).hom, IsCommMonObj.mul_comm]
    smooth := MorphismProperty.of_isPullback (P := @Smooth) h hA.smooth
    proper := MorphismProperty.of_isPullback (P := @IsProper) h hA.proper
    geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h hA.geomConnected }

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeOfIsPullbackSpMapStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_grpObj_isAbelianScheme_of_isPullback_spMap' : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left), IsPullback φ s' A.hom (spMap σ) → ∃ _ : GrpObj (Over.mk s'), IsAbelianScheme (Over.mk s') ∧ SmoothOfRelativeDimension g s' := by
  first | exact @GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap | exact GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap | (intros; apply GlobalTheory.exists_grpObj_isAbelianScheme_of_isPullback_spMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearShortExactCompatible

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem baseChange_middle_equiv_of_exact : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by
  intro R R' _ _ _ W M H _ _ _ _ _ _ W' M' H' _ _ _ _ _ _ i p i' p' a b c hp hip hi' hip' hb hc hW hH
  obtain ⟨eW, heW⟩ := hW
  obtain ⟨eH, heH⟩ := hH
  letI : Module R M' := Module.compHom M' (algebraMap R R')
  haveI : IsScalarTower R R' M' := ⟨fun r s x => by
    show (r • s) • x = algebraMap R R' r • s • x
    rw [Algebra.smul_def, mul_smul]⟩
  let b' : M →ₗ[R] M' :=
    { toFun := b, map_add' := b.map_add, map_smul' := fun r m => b.map_smulₛₗ r m }
  let f : R' ⊗[R] M →ₗ[R'] M' := b'.liftBaseChange R'
  have hf1 : ∀ x, f (1 ⊗ₜ x) = b x := by
    intro x; simp [f, b']
  have hfp : ∀ s, p' (f s) = eH (LinearMap.baseChange R' p s) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      have h1 : (r ⊗ₜ[R] m : R' ⊗[R] M) = r • (1 ⊗ₜ m) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]; simp only [map_smul, hf1, LinearMap.baseChange_tmul, heH, hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hfi : ∀ u, f (LinearMap.baseChange R' i u) = i' (eW u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r w =>
      have h1 : (r ⊗ₜ[R] w : R' ⊗[R] W) = r • (1 ⊗ₜ w) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [h1]; simp only [map_smul, hf1, LinearMap.baseChange_tmul, heW, hb]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hex : Function.Exact (LinearMap.baseChange R' i) (LinearMap.baseChange R' p) := by
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    first | exact lTensor_exact R' hip hp | exact LinearMap.lTensor_exact R' hip hp
  have hsurj : Function.Surjective (LinearMap.baseChange R' p) := by
    rw [LinearMap.baseChange_eq_ltensor]; exact LinearMap.lTensor_surjective R' hp
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    have h0 : LinearMap.baseChange R' p s = 0 := by
      have := hfp s
      rw [hs, map_zero] at this
      exact (LinearEquiv.map_eq_zero_iff eH).1 this.symm
    obtain ⟨u, rfl⟩ := (hex s).1 h0
    have h2 : i' (eW u) = 0 := by rw [← hfi u, hs]
    have h3 : eW u = 0 := hi' (by rw [h2, map_zero])
    rw [(LinearEquiv.map_eq_zero_iff eW).1 h3, map_zero]
  have hsur : Function.Surjective f := by
    intro m'
    obtain ⟨s, hs⟩ := hsurj (eH.symm (p' m'))
    have h0 : p' (m' - f s) = 0 := by
      rw [map_sub, hfp, hs, LinearEquiv.apply_symm_apply, sub_self]
    obtain ⟨w', hw'⟩ := (hip' _).1 h0
    refine ⟨s + LinearMap.baseChange R' i (eW.symm w'), ?_⟩
    rw [map_add (f := _), hfi, LinearEquiv.apply_symm_apply, hw', add_sub_cancel]
  have hbij : Function.Bijective f := ⟨hinj, hsur⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun x => hf1 x⟩

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearShortExactCompatibleStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semilinear_short_exact_compatible : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by
  first | exact @GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact | exact GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact | (intros; apply GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChange

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exact_clAll_toHO1 {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hc : Closed1 (OAff s) = ⊤) :
    Function.Exact (clAll (OAff s) hc) (toHO1 s) := by
  rw [LinearMap.exact_iff]
  change Fil1 (OAff s) = _
  rw [Fil1_eq_range, clAll, LinearMap.range_comp_of_range_eq_top]
  exact LinearEquiv.range _

theorem surjective_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) : Surjective f := by
  have : Surjective (e ≫ f) := by rw [he]; infer_instance
  exact Surjective.of_comp e f

theorem baseChange_HH1_globForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))), (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, e (1 ⊗ₜ c) = pullHH1 h.w c) ∧ ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  intro R _ A _ g hab hsm R' _ _ X' s' φ h
  obtain ⟨inst', hab', hsm'⟩ := GlobalTheory.T.exists_grpObj_isAbelianScheme_of_isPullback_spMap' R A g hab hsm R' (algebraMap R R') X' s' φ h
  obtain ⟨hfr, h0, -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hab hsm
  obtain ⟨hfr', h0', -, -⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R' (Over.mk s') g hab' hsm'
  have hc := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hab hsm
  have hc' := GlobalTheory.T.abelianScheme_globalOneForms_closed R' (Over.mk s') g hab' hsm'
  have hflat : Flat s' := by
    haveI := hsm'
    haveI : Smooth s' := SmoothOfRelativeDimension.smooth g s'
    infer_instance
  have hsurj : Surjective s' := by
    refine surjective_of_section s' (η[Over.mk s']).left ?_
    have := Over.w (η[Over.mk s'])
    simpa using this
  have hW := GlobalTheory.T.exists_equiv_globalOneForms_baseChange R R' A.left X' A.hom s' φ h hfr h0 hfr' h0' hflat hsurj
  refine ⟨?_, hW⟩
  have hH := (GlobalTheory.T.abelian_structure_cohomology_statement R A g hab hsm).2.2.1 R' X' s' φ h
  refine GlobalTheory.T.semilinear_short_exact_compatible R R' (GlobForm A.hom) (HH1 A.hom) (HO1 A.hom) (GlobForm s') (HH1 s') (HO1 s')
    (clAll (OAff A.hom) hc) (toHO1 A.hom) (clAll (OAff s') hc') (toHO1 s')
    (pullForm h.w) (pullHH1 h.w) (pullHO1 h.w)
    (GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hab hsm) (exact_clAll_toHO1 A.hom hc) ?_ (exact_clAll_toHO1 s' hc') ?_ ?_ hW hH
  · exact (ofForm_injective_of_H0Const R' _ (OAff s') h0').comp (LinearEquiv.injective _)
  · intro x
    exact GlobalTheory.T.pull_closed_form_class R R' A.left X' A.hom s' (algebraMap R R') φ h.w hc hc' x
  · intro x
    exact toHO1_pullHH1 h.w x

end GlobalTheory.AbCoh
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamGlobalFormsBaseChangeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.de_rham_global_forms_base_change : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R R'))), (∃ e : R' ⊗[R] HH1 A.hom ≃ₗ[R'] HH1 s', ∀ c, e (1 ⊗ₜ c) = pullHH1 h.w c) ∧ ∃ e : R' ⊗[R] GlobForm A.hom ≃ₗ[R'] GlobForm s', ∀ c, e (1 ⊗ₜ c) = GlobalTheory.CechDR.pullForm h.w c := by
  first | exact @GlobalTheory.AbCoh.baseChange_HH1_globForm | exact GlobalTheory.AbCoh.baseChange_HH1_globForm | (intros; apply GlobalTheory.AbCoh.baseChange_HH1_globForm <;> assumption)
end
end
