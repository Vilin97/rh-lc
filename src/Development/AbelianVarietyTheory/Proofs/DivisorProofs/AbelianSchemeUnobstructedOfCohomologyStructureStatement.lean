module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfConstantDimensionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesO1OfProjectiveRankCupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1StructureBaseChangeExtensionStatement
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtensionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFrames

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem globalFunctionsConstant_of_constant_after_baseChange (s : X ⟶ Sp R) (hU : UConst s) : CohomZeroIsConstants (OAff s) := by
  refine hU R X s (𝟙 X) ?_
  rw [Algebra.algebraMap_self, Cris.spMap_id]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

variable {s : X ⟶ Sp R} {n : ℕ} (fr : Frame (OAff s) n) (hc : CohomZeroIsConstants (OAff s))

theorem coboundaryZero_frame_vectorField_globalForm_eq_zero (i : Fin n) (ω : GlobForm s) : d0 (OAff s) (fun T ↦ fr.δ i T (ω.1 T)) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply, ω.2 φ, fr.nat]
  exact sub_self _

def coef (i : Fin n) (ω : GlobForm s) : R := (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose

theorem coef_spec (i : Fin n) (ω : GlobForm s) (T : AffOp X) :
    fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) (coef fr hc i ω) :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).exists.choose_spec T

theorem coef_eq (i : Fin n) (ω : GlobForm s) (r : R)
    (h : ∀ T, fr.δ i T (ω.1 T) = algebraMap R ((OAff s).obj T) r) : coef fr hc i ω = r :=
  (hc _ (coboundaryZero_frame_vectorField_globalForm_eq_zero fr i ω)).unique (coef_spec fr hc i ω) h

def coefL : GlobForm s →ₗ[R] (Fin n → R) where
  toFun ω i := coef fr hc i ω
  map_add' ω ω' := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    rw [coef_spec fr hc i ω T, coef_spec fr hc i ω' T]
  map_smul' r ω := funext fun i ↦ coef_eq fr hc i _ _ fun T ↦ by
    simp only [Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply,
      smul_eq_mul, map_mul, Algebra.smul_def]
    rw [coef_spec fr hc i ω T]

def sumL : (Fin n → R) →ₗ[R] GlobForm s where
  toFun c := ∑ i, c i • fr.w i
  map_add' c c' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, mul_smul]

theorem sumL_coefL (ω : GlobForm s) : sumL fr (coefL fr hc ω) = ω := by
  apply Subtype.ext
  funext T
  conv_rhs => rw [fr.sum T (ω.1 T)]
  simp only [sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coef_spec, algebraMap_smul]


include fr hc in
theorem projective : Module.Projective R (GlobForm s) :=
  Module.Projective.of_split (coefL fr hc) (sumL fr) (LinearMap.ext (sumL_coefL fr hc))

def back (U : AffOp X) (x : Ω[Sec s U.unop.1⁄R]) : Sec s U.unop.1 ⊗[R] GlobForm s :=
  ∑ i, (fr.δ i U x : Sec s U.unop.1) ⊗ₜ[R] fr.w i

theorem back_add (U : AffOp X) (x y : Ω[Sec s U.unop.1⁄R]) : back fr U (x + y) = back fr U x + back fr U y := by
  simp only [back, map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]


include fr hc in
theorem par (U : AffOp X) : IsBaseChange (Sec s U.unop.1) (evForm s U) := by
  change Function.Bijective (TensorProduct.lift _)
  rw [Function.bijective_iff_has_inverse]
  refine ⟨back fr U, fun t ↦ ?_, fun x ↦ ?_⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp [back]
    | tmul a ω =>
      simp only [TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
        Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
      conv_rhs => rw [← sumL_coefL fr hc ω]
      simp only [back, sumL, coefL, LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← TensorProduct.smul_tmul]
      congr 1
      change fr.δ i U (a • ω.1 U) = coef fr hc i ω • a
      rw [(fr.δ i U).map_smul a (ω.1 U), coef_spec fr hc i ω U, Algebra.smul_def, mul_comm]
      rfl
    | add t t' ht ht' => rw [map_add (f := _), back_add, ht, ht']
  · conv_rhs => rw [fr.sum U x]

    simp only [back, map_sum, TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, LinearMap.flip_apply,
      Algebra.linearMap_apply, Module.algebraMap_end_apply, LinearMap.smul_apply]
    rfl

end GlobalTheory.FormsOnAb

namespace GlobalTheory.FormsOnAb

open GlobalTheory.AbCoh

theorem formSt_of (H : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
      GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) : FormSt := by
  intro R₀ _ A _ g hA hs
  obtain ⟨⟨n, ⟨fr⟩⟩, hU, hP⟩ := H R₀ A g hA hs
  have hc := globalFunctionsConstant_of_constant_after_baseChange A.hom hU
  refine ⟨fun U ↦ par fr hc U, projective fr hc, fun w wm w₁ w₂ hm h1 h2 ↦ ?_⟩
  rw [hm.eq_pullForm, h1.eq_pullForm, h2.eq_pullForm]
  exact hP w

end GlobalTheory.FormsOnAb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalFormsPrimitiveOfFramesStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames : (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → FormSt := by
  first | exact @GlobalTheory.FormsOnAb.formSt_of | exact GlobalTheory.FormsOnAb.formSt_of | (intros; apply GlobalTheory.FormsOnAb.formSt_of <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfFormsStructureStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_forms_structure : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  first | exact @GlobalTheory.Obs.unobDim_of_formSt | exact GlobalTheory.Obs.unobDim_of_formSt | (intros; apply GlobalTheory.Obs.unobDim_of_formSt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingDegreeOneExtension

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem axesE1_of_axesO1 : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  intro hO R₀ R₁ _ _ _ q hq A _ g hab hsm c h₁ h₂
  obtain ⟨B, hB, pr, pr', habB, hsmB, hp, hp', -, -, -, hl, hr⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R₀ R₁ A g hab hsm
  letI : GrpObj B := hB
  obtain ⟨e, he⟩ := GlobalTheory.T.h1_structure_base_change_extension R₀ R₁ q hq
  set c₁ := (e _ _ _ _ _ hp').symm c with hc₁
  have hc : e _ _ _ _ _ hp' c₁ = c := by simp [hc₁]
  have hl' : IsPullO (overW (lift (𝟙 B) 1)) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift (𝟙 A) 1)) (overW (lift (𝟙 B) 1)) hl c₁ 0 ?_
    rw [hc, map_zero]; exact h₁
  have hr' : IsPullO (overW (lift 1 (𝟙 B))) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift 1 (𝟙 A))) (overW (lift 1 (𝟙 B))) hr c₁ 0 ?_
    rw [hc, map_zero]; exact h₂
  have h0 : c₁ = 0 := hO R₁ B g habB hsmB c₁ hl' hr'
  rw [← hc, h0, map_zero]

end GlobalTheory.Obs
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingDegreeOneExtensionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.axes_vanishing_degree_one_extension : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  first | exact @GlobalTheory.Obs.axesE1_of_axesO1 | exact GlobalTheory.Obs.axesE1_of_axesO1 | (intros; apply GlobalTheory.Obs.axesE1_of_axesO1 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfCohomologyStructure

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem abelianUnobstructed_of_struct (hO : GlobalTheory.AbCoh.OStr)
    (hF : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧
        GlobalTheory.AbCoh.PrimF A) : GlobalTheory.Published.AbelianUnobstructed := by
  have hS : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b := by
    intro R _ A _ g hA hg
    obtain ⟨h1, h2, -, -⟩ := hO R A g hA hg
    exact ⟨h1, h2⟩
  exact GlobalTheory.T.abelianSchemeUnobstructed_of_constantDimension (GlobalTheory.T.abelianScheme_unobstructed_of_forms_structure (GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames hF) (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish hS))
    (GlobalTheory.T.axes_vanishing_degree_one_extension (GlobalTheory.T.axesO1_of_projective_rank_cup hS)))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfCohomologyStructureStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_cohomology_structure : GlobalTheory.AbCoh.OStr → (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.abelianUnobstructed_of_struct | exact GlobalTheory.abelianUnobstructed_of_struct | (intros; apply GlobalTheory.abelianUnobstructed_of_struct <;> assumption)
end
end
