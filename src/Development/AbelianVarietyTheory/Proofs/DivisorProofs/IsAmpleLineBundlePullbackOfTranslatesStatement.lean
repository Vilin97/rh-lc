module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslatesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAddInfPreimageSubGrpScheme

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SumAffine

theorem isIso_shear {C : Type*} [Category C] [CartesianMonoidalCategory C] (A T : C) [GrpObj A]
    (b : T ⟶ A) : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)) := by
  refine ⟨lift (fst A T * (snd A T ≫ b⁻¹)) (snd A T), ?_, ?_⟩
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp
  · ext
    · simp [MonObj.comp_mul, GrpObj.comp_inv, mul_assoc]
    · simp

theorem isAffineOpen_preimage_translate (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R)) [IsAffine T.left] (b : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ b)).left ⁻¹ᵁ V) := by
  haveI : IsAffine (Sp R) := by unfold Sp; infer_instance
  haveI : IsAffineHom T.hom := inferInstance
  haveI : IsAffineHom (fst A T).left := by
    change IsAffineHom (pullback.fst A.hom T.hom)
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback A.hom T.hom).flip inferInstance
  haveI := isIso_shear A T b
  have h : fst A T * (snd A T ≫ b) = lift (fst A T * (snd A T ≫ b)) (snd A T) ≫ fst A T := by simp
  haveI : IsAffineHom (fst A T * (snd A T ≫ b)).left := by
    rw [h, Over.comp_left]
    haveI : IsIso (lift (fst A T * (snd A T ≫ b)) (snd A T)).left :=
      inferInstanceAs (IsIso ((Over.forget (Sp R)).map (lift (fst A T * (snd A T ≫ b)) (snd A T))))
    infer_instance
  exact hV.preimage _

theorem isAffineOpen_preimage_add_inf_preimage_sub (R : Type) [CommRing R] (A : Over (Sp R))
    [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens) (hV : IsAffineOpen V) (T : Over (Sp R))
    [IsAffine T.left] (a : T ⟶ A) :
    IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓
      (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  have h1 := isAffineOpen_preimage_translate R A V hV T a
  have h2 := isAffineOpen_preimage_translate R A V hV T a⁻¹
  rw [GrpObj.comp_inv] at h2
  haveI : IsSeparated (snd A T).left := by
    change IsSeparated (pullback.snd A.hom T.hom)
    infer_instance
  haveI : (A ⊗ T).left.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (snd A T).left]
    infer_instance
  exact h1.inf h2

end GlobalTheory.SumAffine
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageAddInfPreimageSubGrpSchemeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAffineOpen_preimage_add_inf_preimage_sub_grpScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsSeparated A.hom] (V : A.left.Opens), IsAffineOpen V → ∀ (T : Over (Sp R)) [IsAffine T.left] (a : T ⟶ A), IsAffineOpen ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub | exact GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub | (intros; apply GlobalTheory.SumAffine.isAffineOpen_preimage_add_inf_preimage_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateMulInvIsNonvanishingLocusSquare

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SquareLocus



theorem translate_mul_inv_isLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (V : A.left.Opens), IsLocus c V → ∀ (T : Over S) (a : T ⟶ A), GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull ((a)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 → IsLocus (2 • GlobalTheory.CechPic.pull (fst A T).left c) ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  intro S _ A _ hA c V hV T a h
  have hsq := GlobalTheory.T.theorem_of_square_cechPicard_translates S A hA c (A ⊗ T) (fst A T) (snd A T ≫ a)
  have e1 : (snd A T ≫ a)⁻¹ = snd A T ≫ a⁻¹ := (GrpObj.comp_inv _ _).symm
  have e2 : (1 : A ⊗ T ⟶ A) = snd A T ≫ (1 : T ⟶ A) := (MonObj.comp_one _).symm
  have h0 : pull (snd A T ≫ a).left c + pull (snd A T ≫ a)⁻¹.left c
      - 2 • pull (1 : A ⊗ T ⟶ A).left c = 0 := by
    rw [e1, e2, Over.comp_left, Over.comp_left, Over.comp_left, pull_comp, pull_comp, pull_comp,
      ← map_nsmul, ← map_add, ← map_sub, h, map_zero]
  have h2 : pull (fst A T * (snd A T ≫ a)).left c + pull (fst A T * (snd A T ≫ a)⁻¹).left c
      = 2 • pull (fst A T).left c := by
    rw [hsq, ← sub_eq_zero, ← h0]
    abel
  have hl := (GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)).left c V hV).add
    (GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)⁻¹).left c V hV)
  rw [h2] at hl
  exact hl

end GlobalTheory.SquareLocus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateMulInvIsNonvanishingLocusSquareStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translate_mul_inv_isNonvanishingLocus_square : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (V : A.left.Opens), IsLocus c V → ∀ (T : Over S) (a : T ⟶ A), GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull ((a)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 → IsLocus (2 • GlobalTheory.CechPic.pull (fst A T).left c) ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  first | exact @GlobalTheory.SquareLocus.translate_mul_inv_isLocus | exact GlobalTheory.SquareLocus.translate_mul_inv_isLocus | (intros; apply GlobalTheory.SquareLocus.translate_mul_inv_isLocus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLineBundlePullbackOfTranslates

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isAmpleLB_pull_fst_of_translates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (c : Pic A.left) (V : A.left.Opens), cls L hL = c → IsAffineOpen V → IsLocus c V → ∀ (T : Over (Sp R)) [IsAffine T.left] (n : ℕ) (a : Fin n → (T ⟶ A)), ⨆ i, ((fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ → (∀ i, GlobalTheory.CechPic.pull (a i).left c + GlobalTheory.CechPic.pull ((a i)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0) → GlobalTheory.IsAmpleLB (L.pull (fst A T).left) := by
  intro R _ _ A _ hA L hL c V hc hV hloc T _ n a hcov hrel
  haveI : IsProper A.hom := hA.proper
  have hL' : (L.pull (fst A T).left).IsLB := LB.isLB_pull hL _
  have h2 : (lbPow (L.pull (fst A T).left) 2).IsLB := GlobalTheory.isLB_lbPow hL' 2
  have hcls : cls _ h2 = 2 • CechPic.pull (fst A T).left c := by
    rw [cls_lbPow hL' 2 h2, cls_pull hL _ hL', hc]
  have hsec : ∀ i, ∃ s : (lbPow (L.pull (fst A T).left) 2).Sec, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s =
      (fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V := fun i =>
    IsLocus.exists_sec h2 (hcls ▸ GlobalTheory.T.translate_mul_inv_isNonvanishingLocus_square (Sp R) A hA c V hloc T (a i) (hrel i))
  choose s hs using hsec
  exact isAmpleLB_of_cover hL' (by norm_num) s (by simp only [hs]; exact hcov)
    fun i => (hs i).symm ▸ GlobalTheory.T.isAffineOpen_preimage_add_inf_preimage_sub_grpScheme R A V hV T (a i)

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLineBundlePullbackOfTranslatesStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAmple_lineBundle_pullback_of_translates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (c : Pic A.left) (V : A.left.Opens), cls L hL = c → IsAffineOpen V → IsLocus c V → ∀ (T : Over (Sp R)) [IsAffine T.left] (n : ℕ) (a : Fin n → (T ⟶ A)), ⨆ i, ((fst A T * (snd A T ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ → (∀ i, GlobalTheory.CechPic.pull (a i).left c + GlobalTheory.CechPic.pull ((a i)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0) → GlobalTheory.IsAmpleLB (L.pull (fst A T).left) := by
  first | exact @GlobalTheory.isAmpleLB_pull_fst_of_translates | exact GlobalTheory.isAmpleLB_pull_fst_of_translates | (intros; apply GlobalTheory.isAmpleLB_pull_fst_of_translates <;> assumption)
end
end
